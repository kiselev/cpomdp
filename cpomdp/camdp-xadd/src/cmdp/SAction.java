//////////////////////////////////////////////////////////////////////
//   Class for stochastic action representation/construction.
//
//////////////////////////////////////////////////////////////////////

// Package definition
package cmdp;

// Packages to import
import java.io.*;
import java.util.*;

import xadd.XADD;
import xadd.XADD.ArithExpr;
import xadd.XADD.BoolDec;

/**
 * Class for stochastic action representation/construction.
 **/
public class SAction {
	/* Local constants */

	/* Local vars */
	public CSMDP _mdp; // MDP of which this action is a part
	public String _sName; // Name of this action
	public HashMap<String, Integer> _hmVar2DD;
	public HashMap<String, Integer> _hmNoise2DD;
	public Integer _reward;

	/**
	 * Constructor
	 **/
	public SAction(CSMDP mdp, String name, HashMap<String, ArrayList> cpt_desc, HashMap<String, ArrayList> cpt_noise, Integer reward) {

		_mdp = mdp;
		_sName = name;
		_hmVar2DD = new HashMap<String, Integer>();
		_hmNoise2DD = new HashMap<String, Integer>();
		_reward = reward;
		buildAction(cpt_desc);
		buildNoise(cpt_noise);
	}

	/**
	 * Build action description DDs
	 **/
	public void buildAction(HashMap<String,ArrayList> cpt_desc) {

		// Head will be for current next-state
		for (Map.Entry<String,ArrayList> e : cpt_desc.entrySet()) {
			
			String var = e.getKey();
			int xadd = _mdp._context.buildCanonicalXADD(e.getValue());
					
			// If a boolean variable, need to construct dual action diagram
			//System.out.println(var + " vs " + _mdp._alBVars);
			if (_mdp._alBVars.contains(var.substring(0, var.length() - 1))) {
				int var_index = _mdp._context.getVarIndex( _mdp._context.new BoolDec(var/* + "'"*/), false);
				int high_branch = xadd;
				int low_branch = _mdp._context.apply(
						_mdp._context.getTermNode(XADD.ONE), high_branch, XADD.MINUS);
				xadd = _mdp._context.getINode(var_index, low_branch, high_branch);
				xadd = _mdp._context.makeCanonical(xadd);
				_hmVar2DD.put(var, xadd);
			} else{
				_hmVar2DD.put(var, xadd);
				}
		}
	}

	public void buildNoise(HashMap<String,ArrayList> cpt_noise) {

		// Head will be for current next-state
		for (Map.Entry<String,ArrayList> e : cpt_noise.entrySet()) {
			
			String var = e.getKey();
			int xadd = _mdp._context.buildCanonicalXADD(e.getValue());
					
			// If a boolean variable, need to construct dual action diagram
			//System.out.println(var + " vs " + _mdp._alBVars);
		/*	if (_mdp._alBVars.contains(var.substring(0, var.length() - 1))) {
				int var_index = _mdp._context.getVarIndex( _mdp._context.new BoolDec(var + "'"), false);
				int high_branch = xadd;
				int low_branch = _mdp._context.apply(
						_mdp._context.getTermNode(XADD.ONE), high_branch, XADD.MINUS);
				xadd = _mdp._context.getINode(var_index, low_branch, high_branch);
				xadd = _mdp._context.makeCanonical(xadd);
				_hmVar2DD.put(var, xadd);
			} else{*/
				_hmNoise2DD.put(var, xadd);
				//}
		}
	}
	
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(_sName + ":\n");
		for (Map.Entry<String,Integer> me : _hmVar2DD.entrySet()) {
			XADD.XADDNode n = _mdp._context.getNode(me.getValue());
			sb.append("*****\n" + me.getKey() + " " + n.collectVars() + ":\n" + 
					  _mdp._context.getString(me.getValue()) + "\n");
		}
		
		XADD.XADDNode r = _mdp._context.getNode(_reward);
		sb.append("*****\nReward: " + r.collectVars() + ":\n" + 
				  _mdp._context.getString(_reward) + "\n");
		
		sb.append("*****\n");

		return sb.toString();
	}
}
