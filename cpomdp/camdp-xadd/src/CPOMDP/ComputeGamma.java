package CPOMDP;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import util.IntTriple;
import xadd.XADD;
import xadd.XADD.ArithExpr;
import xadd.XADD.BoolDec;
import xadd.XADD.DeltaFunctionSubstitution;
import xadd.XADD.DoubleExpr;
import xadd.XADD.OperExpr;
import xadd.XADD.VarExpr;
import xadd.XADD.XADDINode;
import xadd.XADD.XADDNode;
import xadd.XADD.XADDTNode;

public class ComputeGamma {

	XADD _context = null;
	CPOMDP _pomdp = null;
	private IntTriple _contRegrKey = new IntTriple(-1,-1,-1);

	public ComputeGamma(XADD xadd,CPOMDP pomdp)
	{
		_context = xadd;
		_pomdp = pomdp;
	}
	public int computeGamma(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) {

		//first generate relevant observation partitions
		generateRelObs(a,_previousgammaSet_h);
		// for each of the alpha-vectors in the previous gammaset
		int crossSum = _context.getTermNode(XADD.ZERO);
		for (Map.Entry<Integer,Integer> j : _previousgammaSet_h.entrySet())
		{
			XADDNode n = _context.getNode(j.getValue());
			
			//first progress through the observations
			
			
			HashSet<String> state_vars_in_vfun  = n.collectVars();
			_pomdp._logStream.println("** Regressing " + a._sName + "\n- State vars in vfun: " + state_vars_in_vfun);
			
			// prime the result
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
			crossSum = _context.apply(crossSum, q, _context.SUM);
			
		}
		crossSum = _context.apply(a._reward,  
				_context.scalarOp(crossSum, _pomdp._bdDiscount.doubleValue(), XADD.PROD), 
				XADD.SUM);	

    	// Ensure Q-function is properly constrained and minimal (e.g., subject to constraints)
		for (Integer constraint : _pomdp._alConstraints)
			crossSum = _context.apply(crossSum, constraint, XADD.PROD);
		if (_pomdp._alConstraints.size() > 0)
			crossSum = _context.reduceLP(crossSum,_pomdp._alContAllVars);
		
		// Optional Display
		_pomdp._logStream.println("- Q^" + _pomdp._nCurIter + "(" + a._sName + ", " + " )\n" + _context.getString(crossSum));
		
		return crossSum;
	}
	
	private void generateRelObs(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) 
	{

		HashMap<String,ArithExpr> obs_subs = new HashMap<String,ArithExpr>();
		for (int i=0;i<a._contObs.size();i++)
		{
			//first find the obs_subs that are to be substituted in each alpha-vector. 
			//Note that this operation is only for no noise or binary noise
			ArithExpr obs_var = ArithExpr.parse(a._contObs.get(i));
			for (int bo=0;bo<a._boolObs.size();bo++)
			{
				XADDNode obsnode = _context.getNode(a._hmObs2DD.get(a._contObs.get(i)));
				//either a TNode which means no noise, or INODE where there is noise
				if (obsnode instanceof XADDTNode)
				{
					obs_var = getVarCoeff(obs_var,((XADDTNode) obsnode)._expr);
					obs_subs.put(a._contState.get(i), obs_var);
				}
				else if (obsnode instanceof XADDINode)
				{
					XADDTNode high = (XADDTNode) _context.getNode(((XADDINode) obsnode)._high);
					obs_var = getVarCoeff(obs_var,high._expr);
					obs_var.makeCanonical();
					obs_subs.put(a._contState.get(i)+"h", obs_var);
					obs_var = null;
					obs_var = ArithExpr.parse(a._contObs.get(i));
					XADDTNode low = (XADDTNode) _context.getNode(((XADDINode) obsnode)._low);
					obs_var = getVarCoeff(obs_var,low._expr);
					obs_var.makeCanonical();
					obs_subs.put(a._contState.get(i)+"l", obs_var);
				}
			}
		}
		for (Map.Entry<Integer,Integer> j : _previousgammaSet_h.entrySet())
		{
			//find observation  partitions of all the vectors, avoid overlapping
			//keep a hashmap for probability, and hashmap of (state partition it came from and the obs partition )
			XADDNode n = _context.getNode(j.getValue());
			


		}
	}
				

	//returns the state dependent formula instead of the observation-dependant formula from the obs model. 
	// work for sums of products 
	private ArithExpr getVarCoeff(ArithExpr obs_var, ArithExpr _expr) 
	{

		//if high._expr is doubleExpr or VarExpr no extra operation is required
		if (_expr instanceof OperExpr	&& ((OperExpr) _expr)._type == _context.SUM) 
		{
			for (ArithExpr e : ((OperExpr) _expr)._terms) 
			{
				if (e instanceof DoubleExpr) 
				{
					obs_var = ArithExpr.op(obs_var, e, _context.MINUS);
				}
				else if (e instanceof OperExpr) 
				{
					if (e instanceof OperExpr && ((OperExpr) e)._type == _context.PROD)
					{
						for (ArithExpr e1 : ((OperExpr) e)._terms) 
						{
							if (e instanceof DoubleExpr) 
							{
								double d = 1/((DoubleExpr) e)._dConstVal ;
								obs_var = ArithExpr.op(obs_var, d, _context.PROD);
							}
						}
					}
				} 
				else if (e instanceof VarExpr)
				{
					//no new operation is required here
				}
			}
		}
		else if (_expr instanceof OperExpr	&& ((OperExpr) _expr)._type == _context.PROD) 
		{
			for (ArithExpr e : ((OperExpr) _expr)._terms) 
			{
				if (e instanceof DoubleExpr) 
				{
					double d = 1/((DoubleExpr) e)._dConstVal ;
					obs_var = ArithExpr.op(obs_var, d, _context.PROD);
				}
			}	
		}
		return obs_var;
	}



}
