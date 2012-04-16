package CPOMDP.contObs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import org.omg.stub.java.rmi._Remote_Stub;

import cmdp.CMDP;

import CPOMDP.COAction;
import CPOMDP.PartitionObsState;
import CPOMDP.StateObsVector;
import CPOMDP.cpomdp;

import util.IntTriple;
import xadd.XADD;
import xadd.XADD.ArithExpr;
import xadd.XADD.BoolDec;
import xadd.XADD.CompExpr;
import xadd.XADD.Decision;
import xadd.XADD.DeltaFunctionSubstitution;
import xadd.XADD.DoubleExpr;
import xadd.XADD.ExprDec;
import xadd.XADD.OperExpr;
import xadd.XADD.VarExpr;
import xadd.XADD.XADDINode;
import xadd.XADD.XADDNode;
import xadd.XADD.XADDTNode;

public class ContComputeGamma {

	XADD _context = null;
	cpomdp _pomdp = null;
	private IntTriple _contRegrKey = new IntTriple(-1,-1,-1);
	HashMap<Integer,PartitionObsState> _obspartitionset= new HashMap<Integer,PartitionObsState>();
	HashMap<Integer, Integer> newalphas = new HashMap<Integer, Integer>();
	int[] belief = new int[1];
	public ContComputeGamma(XADD xadd,cpomdp pomdp)
	{
		_context = xadd;
		_pomdp = pomdp;
		//1 belief for now: 
		ArrayList l0 =new ArrayList();
		l0.add("[-6 + t*1 <= 0]");
		ArrayList l0t = new ArrayList();
		ArrayList l0f = new ArrayList();
		l0t.add("[-2 + t*1 >= 0]");
		ArrayList l0tt = new ArrayList();
		ArrayList l0tf = new ArrayList();
		l0tt.add("0.25");
		l0tf.add("0");
		l0t.add(l0tt);
		l0t.add(l0tf);
		l0f.add("0");
		l0.add(l0t);
		l0.add(l0f);
		int b0 = _context.buildCanonicalXADD(l0);
		belief[0] = b0;
	}
	public int[] computeGamma(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) {

		//first generate relevant observation partitions
		_obspartitionset= new HashMap<Integer,PartitionObsState>();
		newalphas = new HashMap<Integer, Integer>();
		for (int i=0;i<belief.length;i++)
			generateRelObs(a,_previousgammaSet_h,belief[i]);
		_pomdp._obspartitions.putAll(_obspartitionset);
		for (Map.Entry<Integer,Integer> j : _previousgammaSet_h.entrySet())
		{
			// for each of the alpha-vectors in the previous gammaset:regress alpha's first
			XADDNode n = _context.getNode(j.getValue());			
			
			HashSet<String> state_vars_in_vfun  = n.collectVars();
			_pomdp._logStream.println("** Regressing " + a._sName + "\n- State vars in vfun: " + state_vars_in_vfun);
			
			// prime
			int q = _context.substitute(j.getValue(), _pomdp._hmPrimeSubs); 
			_pomdp._logStream.println("- Primed value function:\n" + _context.getString(q));
			
			// Regress continuous variables first in order given in 
			for (String var : state_vars_in_vfun) {
				if (!_pomdp._hsContSVars.contains(var))
					continue; // Not regressing boolean variables yet, skip

				// Get cpf for continuous var'
				String var_prime = var + "'";
				int var_id = _context.getVarIndex( _context.new BoolDec(var_prime), false);
				Integer dd_conditional_sub = a._hmVar2DD.get(var_prime);

				_pomdp._logStream.println("- Integrating out: " + var_prime + "/" + var_id + " in\n" + _context.getString(dd_conditional_sub));

				// Check cache
				_contRegrKey.set(var_id, dd_conditional_sub, q);
				Integer result = null;
				if ((result = _pomdp._hmContRegrCache.get(_contRegrKey)) != null) {
					q = result;
					continue;
				}
				
				// Perform regression via delta function substitution
				q = _context.reduceProcessXADDLeaf(dd_conditional_sub, 
						_context.new DeltaFunctionSubstitution(var_prime, q), true);
				
				// Cache result
				_pomdp._logStream.println("-->: " + _context.getString(q));
				_pomdp._hmContRegrCache.put(new IntTriple(_contRegrKey), q);
			}
			
			// Regress boolean variables second
			for (String var : state_vars_in_vfun) {
				if (!_pomdp._hsBoolSVars.contains(var))
					continue; // Continuous variables already regressed, skip
			
				// Get cpf for boolean var'
				String var_prime = var + "'";
				int var_id = _context.getVarIndex( _context.new BoolDec(var_prime), false);
				Integer dd_cpf = a._hmVar2DD.get(var_prime);
				
				_pomdp._logStream.println("- Summing out: " + var_prime + "/" + var_id + " in\n" + _context.getString(dd_cpf));
				q = _context.apply(q, dd_cpf, XADD.PROD);
				
				// Following is a safer way to marginalize (instead of using opOut
				// based on apply) in the event that two branches of a boolean variable 
				// had equal probability and were collapsed.
				int restrict_high = _context.opOut(q, var_id, XADD.RESTRICT_HIGH);
				int restrict_low  = _context.opOut(q, var_id, XADD.RESTRICT_LOW);
				q = _context.apply(restrict_high, restrict_low, XADD.SUM);
			}
			
			//finished regress, for each G_{a,j}^h add to the cross-sum result
			newalphas.put(newalphas.size(), q);
			
		}
		//now we have the regressed alpha's and the probability of each observation partition. 
		//for each observation, multipy in the alphas
		//the state in the observation set are not in form of XADD, so need to convert them
		
		int[][] regressedAlpha = new int[_obspartitionset.size()][newalphas.size()];
		for (int i = 0;i< _obspartitionset.size();i++)
		{
			//form an xadd from the state partitions and their probabilities
			HashMap<Integer, StateObsVector> pos = _obspartitionset.get(i)._relObsProb;
			//only has 2 possibilities, either has one partition, where the probability is zero otherwise. Or has overlapped partitions, where the probability 
			//of each state is given
			int nodeO=0;
			if (pos.size()==1)
			{
				Decision d =  _context.new ExprDec(pos.get(0).state);
				nodeO = _context.getVarNode(d,0.0,pos.get(0).probability);
			}
			else if (pos.size()==2)
			{
				Decision d1 = _context.new ExprDec(pos.get(0).state);
				Decision d2 = _context.new ExprDec(pos.get(1).state);
				int intd2 = _context.getVarIndex(d2);
				int intd1 = _context.getVarIndex(d1);
				if (intd1 == Math.abs(intd2))
				{
					if (intd1>0)
					{
						nodeO = _context.getVarNode(d1,pos.get(1).probability,pos.get(0).probability);
					}
					else 
					{
						nodeO = _context.getVarNode(d2,pos.get(0).probability,pos.get(1).probability);
					}
				}

			}
			//any other configuration? 
			for (int j=0;j<newalphas.size();j++)
			{
				regressedAlpha[i][j] = _context.apply(newalphas.get(j), nodeO, _context.PROD);
				regressedAlpha[i][j] = _context.reduceLP(regressedAlpha[i][j] , _pomdp._alContSVars);
			}
		}
		int crossSum[] = new int[(int) Math.pow(newalphas.size(), _obspartitionset.size())];
		//now we need the cross-sum based on different configurations of the observation (alpha1,alpha1,alpha1... alpha2,alpha2,alpha2)
		int counter=0;
		for (int j1=0;j1<newalphas.size();j1++)
			for (int j2=0;j2<newalphas.size();j2++)
				for (int j3=0;j3<newalphas.size();j3++)
					{
						crossSum[counter] = _context.apply(regressedAlpha[0][j1],(_context.apply(regressedAlpha[1][j2], regressedAlpha[2][j3], _context.SUM)),_context.SUM);
						counter++;
					}
		
		for (int j=0;j<crossSum.length;j++)		
			crossSum[j] = _context.apply(a._reward, _context.scalarOp(crossSum[j], _pomdp._bdDiscount.doubleValue(), XADD.PROD), XADD.SUM);	

    	/*// Ensure Q-function is properly constrained and minimal (e.g., subject to constraints)
		for (Integer constraint : _pomdp._alConstraints)
			crossSum = _context.apply(crossSum, constraint, XADD.PROD);
		if (_pomdp._alConstraints.size() > 0)
			crossSum = _context.reduceLP(crossSum,_pomdp._alContAllVars);
		*/
		
		
		return crossSum;
	}
	
	private void generateRelObs(COAction a, HashMap<Integer, Integer> _previousgammaSet_h, int belief) 
	{
		//returns P(each observation partition|b)
		//can check if \int_o\int_s p(o|s)*p(s) =1 
		int check =0;
		Iterator i1 = a._hmObs2DD.entrySet().iterator();
		while (i1.hasNext()) 
		{
			Map.Entry pair1 = (Map.Entry)i1.next();
			check = _context.apply((Integer) pair1.getValue(), belief, _context.PROD);
		}
		for (int i=0;i<_pomdp._alContSVars.size();i++)
			check = _context.computeDefiniteIntegral(check, _pomdp._alContSVars.get(i));
		for (int i=0;i<_pomdp._alContOVars.size();i++)
			check = _context.computeDefiniteIntegral(check, _pomdp._alContOVars.get(i));
		
			
		//1 - for each alpha-vector: first integrate out s'
		HashMap<Integer, Integer> newAlphas = new HashMap<Integer, Integer>();
		ArrayList<XADD.XADDNode> node_list = new ArrayList<XADD.XADDNode>();
		ArrayList<XADD.XADDNode> temp_node_list = new ArrayList<XADD.XADDNode>();
		ArrayList<ArithExpr> temp_subst = new ArrayList<ArithExpr>();
		ArrayList<String> temp_cvar_names = new ArrayList<String>();
		ArrayList<XADD.ArithExpr> subst = new ArrayList<XADD.ArithExpr>();
		ArrayList<String> cvar_names = new ArrayList<String>();
		ArrayList<Integer> node_id_list = new ArrayList<Integer>();

		//substitute and regress observation model, for each variable there is a different set of alpha vectors
		 Iterator it = a._hmObs2DD.entrySet().iterator();
		while (it.hasNext()) 
		{
			Map.Entry pairs = (Map.Entry)it.next();
			XADD.XADDNode n = _context.getNode((Integer) pairs.getValue());
			HashSet<String> vars = n.collectVars();
			int oq=0;
			//for each continuous state variable
			Iterator cs = _pomdp._hmPrimeSubs.entrySet().iterator();
			while (cs.hasNext()) 
			{
				Map.Entry pair2 = (Map.Entry)cs.next();
				oq = _context.substitute((Integer) pairs.getValue(), _pomdp._hmPrimeSubs); 
				temp_node_list = new ArrayList<XADD.XADDNode>();
				temp_subst = new ArrayList<ArithExpr>();
				temp_cvar_names = new ArrayList<String>();
				temp_node_list.add(null);
				temp_subst.add(null);
				temp_cvar_names.add(null);
				Integer dd = a._hmVar2DD.get(pair2.getValue().toString());
				node_id_list.add(dd);
				cvar_names.add(pair2.getValue().toString());
				node_list.add(_context.getNode(dd)); //node_list has all XADDs from action a that are related with valueDD variables
				subst.add(null);
				for (int i = 0; i < node_list.size(); i++) 
				{

					temp_node_list.set(0, node_list.get(i));
					temp_subst.set(0, subst.get(i)); // This is null, right?
					temp_cvar_names.set(0, cvar_names.get(i));
					oq= _context.reduceProcessXADDLeaf(node_id_list.get(i), _context.new DeltaFunctionSubstitution(cvar_names.get(i), oq), true);
					oq = _context.makeCanonical(oq);
				}
			}
		
		//substitute and regress each alpha vector
			for (int i=0;i<_previousgammaSet_h.size();i++)
			{
				//substitute and regress alpha vector
				n = _context.getNode(_previousgammaSet_h.get(i));
				vars = n.collectVars();
				int q=0;
				cs =_pomdp._hmPrimeSubs.entrySet().iterator();
				while (cs.hasNext()) 
				{
					Map.Entry pair2 = (Map.Entry)cs.next();
					node_id_list = new ArrayList<Integer>();
					node_list = new ArrayList<XADD.XADDNode>();
					cvar_names = new ArrayList<String>();
					q = _context.substitute(_previousgammaSet_h.get(i), _pomdp._hmPrimeSubs); 
					temp_node_list = new ArrayList<XADD.XADDNode>();
					temp_subst = new ArrayList<ArithExpr>();
					temp_cvar_names = new ArrayList<String>();
					temp_node_list.add(null);
					temp_subst.add(null);
					temp_cvar_names.add(null);
					Integer dd = a._hmVar2DD.get(pair2.getValue().toString());
					node_id_list.add(dd);
					cvar_names.add(pair2.getValue().toString());
					node_list.add(_context.getNode(dd)); //node_list has all XADDs from action a that are related with valueDD variables
					subst.add(null);
					for (int k = 0; k < node_list.size(); k++) 
					{
						temp_node_list.set(0, node_list.get(k));
						temp_subst.set(0, subst.get(k)); // This is null, right?
						temp_cvar_names.set(0, cvar_names.get(k));
						q= _context.reduceProcessXADDLeaf(node_id_list.get(k), _context.new DeltaFunctionSubstitution(cvar_names.get(k), q), true);
						q = _context.makeCanonical(q);
					}
				}		
			//multiply observation model and alpha vector: 
			q = _context.apply(q, oq, _context.PROD);
			newAlphas.put(newAlphas.size(), q);
			}
			//for all alphas, for all observation variables
		}
		
		//2- for this belief, integrate out s for all newalpha's
		for (int i=0;i< newAlphas.size();i++)
		{
			int beforeInt , afterInt = 0;
			for (int j=0;j<_pomdp._alContSVars.size();j++)
			{
				if (afterInt>0) beforeInt = _context.apply(afterInt, belief, _context.PROD);
				beforeInt = _context.apply(newAlphas.get(i), belief, _context.PROD);
				afterInt =_context.computeDefiniteIntegral(beforeInt,_pomdp._alContSVars.get(j));
				afterInt = _context.reduceLP(afterInt, _pomdp._alContAllVars);
				//or assign a new array for delta's but no need to keep them
			}
			newAlphas.put(i, afterInt);
		}
		// 3- take maximum over delta functions which are stored in newalphas
		int counter =0;
		int max = 0;
		while (counter<newAlphas.size())
		{
			if (max!=0) max = _context.apply(newAlphas.get(counter), max, _context.MAX);
			max = _context.apply(newAlphas.get(counter), newAlphas.get(counter+1), _context.MAX);
			counter+=2;
		}
		
		//4- compute probability of each case partition of max
	}

}