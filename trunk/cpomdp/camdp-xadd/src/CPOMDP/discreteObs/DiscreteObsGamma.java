package CPOMDP.discreteObs;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import org.omg.stub.java.rmi._Remote_Stub;

import CPOMDP.COAction;
import CPOMDP.cpomdp;
import CPOMDP.PartitionObsState;
import CPOMDP.StateObsVector;

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

public class DiscreteObsGamma {

	XADD _context = null;
	cpomdp _pomdp = null;
	private IntTriple _contRegrKey = new IntTriple(-1,-1,-1);
	HashMap<Integer, Integer> newalphas = new HashMap<Integer, Integer>();
	public DiscreteObsGamma(XADD xadd,cpomdp pomdp)
	{
		_context = xadd;
		_pomdp = pomdp;
	}
	public int[] computeGamma(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) {

		//first generate relevant observation partitions
		newalphas = new HashMap<Integer, Integer>();

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
		
		int[][] regressedAlpha = new int[a._hmObs2DD.size()][newalphas.size()];
		int i=0;
		for (Entry<String, Integer> obs:a._hmObs2DD.entrySet())
		{
			for (int j=0;j<newalphas.size();j++)
			{
				regressedAlpha[i][j] = _context.apply(newalphas.get(j), obs.getValue(), _context.PROD);
				regressedAlpha[i][j] = _context.reduceLP(regressedAlpha[i][j] );
			}
			i++;
		}
		int crossSum[] = new int[(int) Math.pow(newalphas.size(), a._hmObs2DD.size())];
		//now we need the cross-sum based on different configurations of the observation (alpha1,alpha1,alpha1... alpha2,alpha2,alpha2)
		//for 3 observations, we need three loops here, just change number of loops
		int counter=0;
		for (int j1=0;j1<newalphas.size();j1++)
			for (int j2=0;j2<newalphas.size();j2++)
				//for (int j3=0;j3<newalphas.size();j3++)
					{
						//crossSum[counter] = _context.apply(regressedAlpha[0][j1],(_context.apply(regressedAlpha[1][j2], regressedAlpha[2][j3], _context.SUM)),_context.SUM);
						crossSum[counter] = _context.apply(regressedAlpha[0][j1],regressedAlpha[1][j2],_context.SUM);
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
	
	

}
