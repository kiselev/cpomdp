package CPOMDP;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import org.omg.stub.java.rmi._Remote_Stub;

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

public class ComputeGamma {

	XADD _context = null;
	CPOMDP _pomdp = null;
	private IntTriple _contRegrKey = new IntTriple(-1,-1,-1);
	HashMap<Integer,PartitionObsState> _obspartitionset= new HashMap<Integer,PartitionObsState>();
	HashMap<Integer, Integer> newalphas = new HashMap<Integer, Integer>();
	public ComputeGamma(XADD xadd,CPOMDP pomdp)
	{
		_context = xadd;
		_pomdp = pomdp;
	}
	public int[] computeGamma(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) {

		//first generate relevant observation partitions
		_obspartitionset= new HashMap<Integer,PartitionObsState>();
		newalphas = new HashMap<Integer, Integer>();
		generateRelObs(a,_previousgammaSet_h);
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
	
	private void generateRelObs(COAction a, HashMap<Integer, Integer> _previousgammaSet_h) 
	{
		//first find the set of observation substitutes for state variables 
		HashMap<String,ArithExpr> obs_subs = null;
		boolean low = true;
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
					obs_subs = new HashMap<String,ArithExpr>();
					obs_var = getVarCoeff(obs_var,((XADDTNode) obsnode)._expr);
					obs_subs.put(a._contState.get(i), obs_var);
				}
				else if (obsnode instanceof XADDINode)
				{
					obs_subs = new HashMap<String,ArithExpr>();
					XADDTNode high = (XADDTNode) _context.getNode(((XADDINode) obsnode)._high);
					obs_var = getVarCoeff(obs_var,high._expr);
					obs_var.makeCanonical();
					obs_subs.put(a._contState.get(i), obs_var);
					
					low = false;
				}
			}
		}
		substituteVar(a,_previousgammaSet_h, obs_subs,1);
		if (low ==false)
		{
			for (int i=0;i<a._contObs.size();i++)
			{
				//first find the obs_subs that are to be substituted in each alpha-vector. 
				//Note that this operation is only for no noise or binary noise
				ArithExpr obs_var = ArithExpr.parse(a._contObs.get(i));
				for (int bo=0;bo<a._boolObs.size();bo++)
				{
					XADDNode obsnode = _context.getNode(a._hmObs2DD.get(a._contObs.get(i)));
					obs_subs = new HashMap<String,ArithExpr>();
					obs_var = null;
					obs_var = ArithExpr.parse(a._contObs.get(i));
					XADDTNode low1 = (XADDTNode) _context.getNode(((XADDINode) obsnode)._low);
					obs_var = getVarCoeff(obs_var,low1._expr);
					obs_var.makeCanonical();
					obs_subs.put(a._contState.get(i), obs_var);
				}
			}
			substituteVar(a,_previousgammaSet_h, obs_subs,0);
		}
	}
	public void substituteVar(COAction a, HashMap<Integer, Integer> _previousgammaSet_h, HashMap<String,ArithExpr> obs_subs,int branch)
	{
		//find observation  partitions of all the vectors, avoid overlapping
		for (int j=0;j<_previousgammaSet_h.size();j++)
		{
			//keep a hashmap for probability, and hashmap of (state partition it came from and the obs partition )
			int subst_obs = _context.substitute(_previousgammaSet_h.get(j), obs_subs);
			XADDNode n = _context.getNode(_previousgammaSet_h.get(j));
			XADDNode o = _context.getNode(subst_obs);
			if (n instanceof XADDTNode)
			{//there is no phi in a Tnode, don't add to observation partitions
			}
			if (n instanceof XADDINode)
			{
				int sp = ((XADDINode)n)._var;
				int op = ((XADDINode)o)._var;
				Decision d =  _context._alOrder.get(sp);
				Decision od=  _context._alOrder.get(op);
				double low1=0,high1=0;
				if (d instanceof ExprDec)
				{
					ExprDec e = (ExprDec) d;
					ExprDec oe = (ExprDec) od;
					oe = (ExprDec) oe.makeCanonical();
					PartitionObsState obsS;
					for (int bo=0;bo<a._boolObs.size();bo++)
					{
						String b = a._boolObs.get(bo)+"'";
						XADDINode booleanNode = (XADDINode) _context.getNode(a._hmVar2DD.get(b));
						XADDTNode low = (XADDTNode) _context.getNode(booleanNode._low);
						XADDTNode high = (XADDTNode) _context.getNode(booleanNode._high);
						 if (low._expr instanceof DoubleExpr)
							 low1 = ((DoubleExpr)low._expr)._dConstVal;
						 if (high._expr instanceof DoubleExpr)
							 high1 = ((DoubleExpr)high._expr)._dConstVal;
						//low branch, low probability, 
						 //assume one noise model for every action (for all state-observations)
						 //low branch uses the negation of the actual expression
						 int sign = oe._expr._type;
						 CompExpr negoeC = new CompExpr(oe._expr._type, oe._expr._lhs, oe._expr._rhs);
						 negoeC._type= negoeC.flipCompOper(negoeC._type);
						 /*if ( sign == _context.LT_EQ || sign == _context.LT) 
							 negoeC._type = _context.GT_EQ;
						 else if ( sign == _context.GT_EQ || sign == _context.GT) 
							 negoeC._type = _context.LT_EQ;*/
						int oo = overlapObservation(negoeC);
						CompExpr negoeS = new CompExpr(e._expr._type, e._expr._lhs, e._expr._rhs);
						if (branch==0) 
							negoeS._type = negoeS.flipCompOper(negoeS._type);
						if (oo != -1)
						{
							obsS = _obspartitionset.get(oo);
							StateObsVector so = new StateObsVector(negoeS, negoeC,low1);
							obsS.setnewPartition(so);
							_obspartitionset.put(oo, obsS);

						}
						else //no overlap, add new partition
						{
							StateObsVector so = new StateObsVector(negoeS, negoeC,low1);
							obsS = new PartitionObsState();
							obsS.setnewPartition(so);
							_obspartitionset.put(_obspartitionset.size(), obsS);	
						}
						//high branch, low probability, assume one noise model for every action (for all state-observations)
						oo = overlapObservation(oe._expr);
						if (oo!=-1)
						{
							obsS = _obspartitionset.get(oo);
							StateObsVector so = new StateObsVector(negoeS, oe._expr,high1);
							obsS.setnewPartition(so);
							_obspartitionset.put(oo, obsS);
						}
						else //no overlap, add new partition
						{
							StateObsVector so = new StateObsVector(negoeS, oe._expr,high1);
							obsS = new PartitionObsState();
							obsS.setnewPartition(so);
							_obspartitionset.put(_obspartitionset.size(), obsS);
						}
						
					}
				
				}
			}
		}
		
	}
				

	private int overlapObservation(CompExpr oe) {
		//compare all observation partitions < or > and if overlaps, return the number of that partitionset
		for (int i=0;i<_obspartitionset.size();i++)
		{
			PartitionObsState pos = _obspartitionset.get(i);
			for (int j=0;j<pos.sizePartitionObsState();j++)
			{
				StateObsVector sov = pos.get_relObsProb(j);
				//TODO: assume only one obs variable
				//compare sov.obs with oe, if equal or different types of overlapping
				//both are canonical so only need to consider the double expr on the left hand side
				if (sov.obs._type == oe._type)
				{
					//only overlap if the double constant is equal
					if ((sov.obs._lhs instanceof OperExpr)&&(oe._lhs instanceof OperExpr))
					{
						for (ArithExpr e1 : ((OperExpr) sov.obs._lhs)._terms) 
							if (e1 instanceof DoubleExpr) 
								for (ArithExpr e2 : ((OperExpr) oe._lhs)._terms) 
								{
									if (e2 instanceof DoubleExpr) 
									{
										if (((DoubleExpr) e1)._dConstVal == ((DoubleExpr) e2)._dConstVal)
											return j;
									}
								}
							
						
					}
				}
				else 
				{
					//overlap if 1: <= and 2:>= and 1's constant > 2's constant (note they are negative numbers)
					//or if 1: >= and 2:<= and 1's constant is smaller than 2's constant ( for negative numbers it is opposite) 
					if ((sov.obs._lhs instanceof OperExpr)&&(oe._lhs instanceof OperExpr))
					{
						if (sov.obs._type == _context.LT_EQ || sov.obs._type == _context.LT)
						{
							for (ArithExpr e1 : ((OperExpr) oe._lhs)._terms) 
								if (e1 instanceof DoubleExpr) 
									for (ArithExpr e2 : ((OperExpr) sov.obs._lhs)._terms) 
									{
										if (e2 instanceof DoubleExpr) 
										{
											//consider positive and negative numbers here
											if ((((DoubleExpr) e1)._dConstVal>=0) && (((DoubleExpr) e2)._dConstVal>=0))
												{
												if (((DoubleExpr) e1)._dConstVal<((DoubleExpr) e2)._dConstVal)
													return j;
												}
											else if ((((DoubleExpr) e1)._dConstVal<=0) && (((DoubleExpr) e2)._dConstVal<=0))
											{
												if (((DoubleExpr) e1)._dConstVal>((DoubleExpr) e2)._dConstVal)
													return j;
											}
											else if ((((DoubleExpr) e1)._dConstVal<=0) && (((DoubleExpr) e2)._dConstVal>=0))
											{
													return j;
											}
											//no forth comparison
											
										}
									}
								
						}
						else if (sov.obs._type == _context.GT_EQ || sov.obs._type == _context.GT)
						{
							for (ArithExpr e1 : ((OperExpr) oe._lhs)._terms) 
								if (e1 instanceof DoubleExpr) 
									for (ArithExpr e2 : ((OperExpr) sov.obs._lhs)._terms) 
									{
										if (e2 instanceof DoubleExpr) 
										{
											//consider positive and negative numbers here
											if ((((DoubleExpr) e1)._dConstVal>=0) && (((DoubleExpr) e2)._dConstVal>=0))
												{
												if (((DoubleExpr) e1)._dConstVal>((DoubleExpr) e2)._dConstVal)
													return j;
												}
											else if ((((DoubleExpr) e1)._dConstVal<=0) && (((DoubleExpr) e2)._dConstVal<=0))
											{
												if (((DoubleExpr) e1)._dConstVal<((DoubleExpr) e2)._dConstVal)
													return j;
											}
											else if ((((DoubleExpr) e1)._dConstVal>=0) && (((DoubleExpr) e2)._dConstVal<=0))
											{
													return j;
											}
											//no forth comparison
											
										}
									}
						}
						
						
					}
				}

			}
		}
		return -1;
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
