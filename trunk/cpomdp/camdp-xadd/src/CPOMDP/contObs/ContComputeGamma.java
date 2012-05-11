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
	HashMap<Integer,ObsPartition> _obspartitionset= new HashMap<Integer,ObsPartition>();
	ObsPartition partition = new ObsPartition();
	int partitionNo =0;
	int[] regressedObservation;
	HashMap<Integer, Integer> newalphas = new HashMap<Integer, Integer>();
	public ContComputeGamma(XADD xadd,cpomdp pomdp)
	{
		_context = xadd;
		_pomdp = pomdp;
		
	}
	public int[] computeGamma(COAction a, HashMap<Integer, Integer> _previousgammaSet_h, int belief) {

		//first generate relevant observation partitions
		_obspartitionset= new HashMap<Integer,ObsPartition>();
		regressedObservation = new int[a._hmObs2DD.size()];
		newalphas = new HashMap<Integer, Integer>();
		generateRelObs(a,_previousgammaSet_h, belief);
		//_pomdp._obspartitions.putAll(_obspartitionset);
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

			double d = _obspartitionset.get(i).getProbability();
			if (d< 0.00000001) d = 0.0;
			int dd = _context.getTermNode(ArithExpr.parse(Double.toString(d)));
			for (int j=0;j<newalphas.size();j++)
			{
				regressedAlpha[i][j] = _context.apply(newalphas.get(j), dd, _context.PROD);
				regressedAlpha[i][j] = _context.reduceLP(regressedAlpha[i][j] , _pomdp._alContSVars);
			}
		}
		/*int crossSum1[] = new int[(int) Math.pow(newalphas.size(), _obspartitionset.size())];
		//now we need the cross-sum based on different configurations of the observation (alpha1,alpha1,alpha1... alpha2,alpha2,alpha2)
		int counter=0;
		for (int j1=0;j1<newalphas.size();j1++)
			for (int j2=0;j2<newalphas.size();j2++)
				for (int j3=0;j3<newalphas.size();j3++)
					{
						crossSum1[counter] = _context.apply(regressedAlpha[0][j1], regressedAlpha[1][j2],_context.SUM);
						crossSum1[counter] = _context.apply(regressedAlpha[2][j3], crossSum1[counter],_context.SUM);
						counter++;
					}*/
		//TODO:permutation of o's where each element has alpha choices 
		int crossSum[] = new int[(int) Math.pow(newalphas.size(), _obspartitionset.size())];
		//now we need the cross-sum based on different configurations of the observation (alpha1,alpha1,alpha1... alpha2,alpha2,alpha2)
		for (int k=0;k<crossSum.length;k++)
			crossSum[k] = _context.getTermNode(_context.ZERO);
		for (int i=0;i<_obspartitionset.size();i++)
		{
			int q = (int) Math.pow(newalphas.size(), _obspartitionset.size()-i-1);
			for (int j=0;j<newalphas.size();j++)
				for (int p=0;p<(crossSum.length / (newalphas.size()*q));p++)
				{
					//int sum =_context.getTermNode(_context.ZERO);;
					for (int k=((p*newalphas.size()+j)*q);k<((p*newalphas.size()+j+1)*q);k++)
					{
						if (crossSum[k]==_context.getTermNode(_context.ZERO))
						{
							crossSum[k] = regressedAlpha[i][j];
							//crossSum[k] = sum;
						}
						else 
							crossSum[k] = _context.apply(regressedAlpha[i][j],crossSum[k],_context.SUM);
					}

				}

		}
		/*for (int k=0;k<crossSum.length;k++)
			crossSum[k] = _context.reduceLP(crossSum[k], _pomdp._alContAllVars);*/

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


	/*public  int[] crossSum(int  regressedAlpha[][], int  curIdx, int  cs[], int  csSize)
	{
		if  (curIdx == regressedAlpha.length)
			return  cs;
		if  (curIdx == 0)
		{ //first array: we only add its values to the cs  array.
			for  (int  i = 0 ; i < regressedAlpha.length  ; i++)
				cs[i] = _context.apply(regressedAlpha[i][curIdx],cs[i],_context.SUM);
			cs = crossSum(regressedAlpha, curIdx + 1, cs, regressedAlpha[curIdx].length);
		} 
		else  
		{
			int  temp[] = new  int[csSize * regressedAlpha[curIdx].length];
			int  counter = 0;
			for  (int  i = 0; i < regressedAlpha[curIdx].length; i++){
				for  (int  j=0; i < csSize; j++){
						temp[counter++] = regressedAlpha[i][curIdx] * cs[j];
				}
			}
			for  (int  i = 0; i < temp.length  ; i++)
				cs[i] =_context.apply(temp[i],cs[i],_context.SUM);
			cs = crossSum(regressedAlpha, curIdx + 1, cs, temp.length);
		}
		return  cs;
	}*/



	private void generateRelObs(COAction a, HashMap<Integer, Integer> _previousgammaSet_h, int belief) 
	{
		//returns P(each observation partition|b)
		//can check if \int_o\int_s p(o|s')*p(s)p(s'|s) =1 
		/*int check =0;
		Iterator i1 = a._hmObs2DD.entrySet().iterator();
		while (i1.hasNext()) 
		{
			Map.Entry pair1 = (Map.Entry)i1.next();
			check = _context.apply((Integer) pair1.getValue(), belief, _context.PROD);
		}
		for (int i=0;i<_pomdp._alContSVars.size();i++)
			check = _context.computeDefiniteIntegral(check, _pomdp._alContSVars.get(i));
		for (int i=0;i<_pomdp._alContOVars.size();i++)
			check = _context.computeDefiniteIntegral(check, _pomdp._alContOVars.get(i));*/


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
		int cc =0;
		while (it.hasNext()) 
		{
			Map.Entry pairs = (Map.Entry)it.next();
			String obsString = (String) pairs.getKey();
			XADD.XADDNode n = _context.getNode((Integer) pairs.getValue());
			HashSet<String> vars = n.collectVars();
			//int oq=0;
			//for each continuous state variable, only consider the relevent state variable ((fo -> f) not p)
			Iterator cs = _pomdp._hmPrimeSubs.entrySet().iterator();
			while (cs.hasNext()) 
			{
				Map.Entry pair2 = (Map.Entry)cs.next();
				if (obsString.equals((String)pair2.getKey() + "o"))
				{
					int oq=0;
					oq = _context.substitute((Integer) pairs.getValue(), _pomdp._hmPrimeSubs); 
					node_list = new ArrayList<XADD.XADDNode>();
					cvar_names = new ArrayList<String>();
					node_id_list = new ArrayList<Integer>();
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
						regressedObservation[cc++] = oq;
					}
				}
			}
		}
			//substitute and regress each alpha vector
		for (int i=0;i<_previousgammaSet_h.size();i++)
		{
				//substitute and regress alpha vector
				XADD.XADDNode n = _context.getNode(_previousgammaSet_h.get(i));
				HashSet<String> vars = n.collectVars();
				int q= _context.substitute(_previousgammaSet_h.get(i), _pomdp._hmPrimeSubs); 
				Iterator cs =_pomdp._hmPrimeSubs.entrySet().iterator();
				while (cs.hasNext()) 
				{
					Map.Entry pair2 = (Map.Entry)cs.next();
					node_id_list = new ArrayList<Integer>();
					node_list = new ArrayList<XADD.XADDNode>();
					cvar_names = new ArrayList<String>();
					/*if (q>0) q = _context.substitute(q, _pomdp._hmPrimeSubs); 
					else q = _context.substitute(_previousgammaSet_h.get(i), _pomdp._hmPrimeSubs); */
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
				int oq = regressedObservation[0];
				for (int j=1;j<regressedObservation.length;j++)
					oq = _context.apply(oq, regressedObservation[j], _context.PROD);
				q = _context.apply(q,oq, _context.PROD);
				boolean alreadyInAlpha = false;
				for (int k=0;k<newAlphas.size();k++)
					if (newAlphas.get(k).equals(q)) alreadyInAlpha = true;
				if (!alreadyInAlpha) newAlphas.put(newAlphas.size(), q);
			}
			//for all alphas, for all observation variables
		

		//2- for this belief, integrate out all continuous states for all newalpha's
		for (int i=0;i< newAlphas.size();i++)
		{
			int afterInt = 0;
			int beforeInt = _context.apply(newAlphas.get(i), belief, _context.PROD);
			for (int j=0;j<_pomdp._alContSVars.size();j++)
			{
				/*if (afterInt>0) 
					beforeInt = _context.apply(afterInt, belief, _context.PROD);
				else beforeInt = _context.apply(newAlphas.get(i), belief, _context.PROD);*/
				if (afterInt>0) 
					afterInt =_context.computeDefiniteIntegral(afterInt,_pomdp._alContSVars.get(j));
				else afterInt =_context.computeDefiniteIntegral(beforeInt,_pomdp._alContSVars.get(j));
				afterInt = _context.reduceLP(afterInt, _pomdp._alContAllVars);
				//or assign a new array for delta's but no need to keep them
			}
			newAlphas.put(i, afterInt);
		}
		// 3- take maximum over delta functions which are stored in newalphas
		int counter =0;
		int max = 0;
		while (counter<newAlphas.size()/2)
		{
			if (max!=0) max = _context.apply(newAlphas.get(counter), max, _context.MAX);
			else max = _context.apply(newAlphas.get(counter), newAlphas.get(counter+1), _context.MAX);
			counter+=2;
		}
		// if it did not have at least 2 alphas: 
		if (max==0)
		{
			max = newAlphas.get(0);
		}
		//4- compute probability of each case partition of max
		partition = new ObsPartition();
		partitionNo =0;
		reduceProbability(max,a,belief);
	}
	private int reduceProbability(int node_id,COAction a,int b) {
		Integer ret = null;
		XADDNode n = _context._hmInt2Node.get(node_id);
		if (n == null) 
		{
			System.out.println("ERROR: " + node_id + " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		if (n instanceof XADDTNode)
		{
			//compute probability 
			int check =0;
			//int cc=0;
			//Iterator i1 = a._hmObs2DD.entrySet().iterator();
			//while (i1.hasNext()) 
			//{
				//Map.Entry pair1 = (Map.Entry)i1.next();
				//check = _context.apply((Integer) pair1.getValue(), b, _context.PROD);
				int oq = regressedObservation[0];
				for (int cc=1;cc<regressedObservation.length;cc++)
					oq = _context.apply(regressedObservation[cc], oq, _context.PROD);
				check = _context.apply(oq, b, _context.PROD);
				//cc++;
			//}
				for (int i=0;i<_pomdp._alContSVars.size();i++)
					check = _context.computeDefiniteIntegral(check, _pomdp._alContSVars.get(i));
				check = _context.reduceLP(check, _pomdp._alContAllVars);
				//multiply indicator

				for (Map.Entry<Decision, Boolean> me : partition.get_decisions().entrySet()) 
				{
					double high_val = me.getValue() ? 1d : 0d;
					double low_val = me.getValue() ? 0d : 1d;
					check = _context.apply(check,_context.getVarNode(me.getKey(), low_val, high_val), _context.PROD);
				}
				//integrate only this observation
				//check = _context.computeDefiniteIntegral(check,(String)pair1.getKey());
				for (int i=0;i<_pomdp._alContOVars.size();i++)
				check = _context.computeDefiniteIntegral(check, _pomdp._alContOVars.get(i));
				System.out.println("AFTER INTEGRATION CHECK: "+ check);
				check = _context.reduceLP(check, _pomdp._alContAllVars);
				XADDTNode t = (XADDTNode) _context.getNode(check);
				partition.setProbability(((DoubleExpr) t._expr)._dConstVal);
				if (partition.getProbability()>0 && partition.getProbability()<1)
				{
					ObsPartition obsP = new ObsPartition(partition.probability,partition.decisions);
					_obspartitionset.put(partitionNo, obsP);
					partitionNo++;
				}
				//partition = new ObsPartition();
			//}
			return node_id; 
		}


		XADDINode inode = (XADDINode) n;
		Decision d = _context._alOrder.get(inode._var);
		partition.decisions.put(d, false);
		int low = reduceProbability(inode._low,a,b);
		partition.decisions.remove(d);
		partition.decisions.put(d, true);
		int high = reduceProbability(inode._high,a,b);
		partition.decisions.remove(d);

		// For now we'll only do linearization of quadratic decisions
		ret = _context.getINode(inode._var, low, high);
		return ret;

	}



}
