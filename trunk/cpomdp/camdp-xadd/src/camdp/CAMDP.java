package camdp;

// Packages to import
import graph.Graph;

import java.io.*;
import java.util.*;

import java.math.BigDecimal;
import java.text.DecimalFormat;

import util.IntTriple;
import xadd.TestXADDDist;
import xadd.XADD;
import xadd.XADD.*;
import cmdp.HierarchicalParser;

/**
 * Main Continuous State and Action MDP (CAMDP) dynamic programming solution class
 * 
 * @version 1.0
 * @author Zahra Zamani
 * @author Scott Sanner
 * @language Java (JDK 1.5)
 * 
 * TODO: Dump dot file
 * TODO: Reintroduce policy annotation
 * TODO: Allow next-state dependent rewards
 * TODO: Allow alternate initialization of V^0 in input file
 * TODO: Seems to be a 0 always maxed in as minimum value -- see Rover-nonlinear2, always V > 0
 * TODO: Believe return XADDs from max_y yields 0's where we don't want them 
 * TODO: For LB < ROOT < UB, might suppress LB < UB constraints
 * TODO: Allow conditioning reward on next state
 **/
public class CAMDP {

	/* Constants */
	//public final static String RESULTS_DIR = "results"; // Diagnostic output destination
	
	public final static boolean DISPLAY_PREMAX_Q = false;
	public final static boolean DISPLAY_POSTMAX_Q = false;
	public final static boolean DISPLAY_V = true;
	public final static boolean DISPLAY_MAX = false;

	//to check for redundancy as well as consistency 
	public boolean REDUNDANDY_CHECK = false;
	/* Maintain an explicit policy? */
	public final static boolean MAINTAIN_POLICY = false;
	
	/* Cache maintenance */
	public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < amt

	/* For printing */
	public static DecimalFormat _df = new DecimalFormat("#.###");
	public static PrintStream _logStream = null;
	
	/* Static variables */
	public static long _lTime; // For timing purposes
	public static Runtime RUNTIME = Runtime.getRuntime();

	/* Local vars */
	public boolean DISPLAY_2D = false;
	public boolean DISPLAY_3D = false;

	public String _problemFile = null;
	//public String _logFileRoot = null;
	public XADD _context = null;
	public HashSet<String> _hsBoolSVars;
	public HashSet<String> _hsContSVars;
	public HashSet<String> _hsContAVars;

	public ArrayList<String> _alBoolSVars; // Retain order given in MDP file
	public ArrayList<String> _alContSVars; // Retain order given in MDP file
	public ArrayList<String> _alContAVars; // Retain order given in MDP file
	public ArrayList<String> _alContAllVars; // Retain order given in MDP file
	
	public Integer _valueDD; // The resulting value function once this CMDP has
	public Integer _maxDD;
	public Integer _prevDD;
	public BigDecimal _bdDiscount; // Discount (gamma) for CMDP
	public Integer    _nMaxIter;   // Number of iterations for CMDP
	public Integer    _nCurIter;   // Number of iterations for CMDP

	public HashMap<String,ArithExpr>  _hmPrimeSubs;
	public HashMap<String,CAction>    _hmName2Action;
	public HashMap<IntTriple,Integer> _hmContRegrCache;
	public ArrayList<Integer>         _alConstraints;
	
	public ComputeQFunction _qfunHelper = null;

	////////////////////////////////////////////////////////////////////////////
	// Constructors
	////////////////////////////////////////////////////////////////////////////

	/**
	 * Constructor - filename
	 **/
	public CAMDP(String filename) {
		this(filename, HierarchicalParser.ParseFile(filename));
	}

	/**
	 * Constructor - pre-parsed file
	 **/
	private CAMDP(String file_source, ArrayList input) {
		
		// Basic initializations
		_problemFile = file_source;
		//_logFileRoot = InsertDirectory(_problemFile, RESULTS_DIR).replace("-", "_");
		_context = new XADD();
		_prevDD = _maxDD = _valueDD = null;
		_bdDiscount = new BigDecimal("" + (-1));
		_nMaxIter = null;
		_hmName2Action = new HashMap<String,CAction>();

		// Setup CAMDP according to parsed file contents
		ParseCAMDP parser = new ParseCAMDP(this);
		parser.buildCAMDP(input);
		_context._hmMaxVal = parser._maxCVal;
		_context._hmMinVal = parser._minCVal;
		_context._alBooleanVars = parser.getBVars();
		_alConstraints = parser.getConstraints();
		_nMaxIter = parser.getIterations();
		_bdDiscount = parser.getDiscount();
		_hmName2Action = parser.getHashmap();
		_hmContRegrCache = new HashMap<IntTriple,Integer>();
		
		// Setup variable sets and lists
		_hsBoolSVars = new HashSet<String>(Intern(parser.getBVars()));
		_hsContSVars = new HashSet<String>(Intern(parser.getCVars()));
		_hsContAVars = new HashSet<String>(Intern(parser.getAVars()));
		_alBoolSVars = new ArrayList<String>(Intern(parser.getBVars())); // Retain order given in MDP file
		_alContSVars = new ArrayList<String>(Intern(parser.getCVars())); // Retain order given in MDP file
		_alContAVars = new ArrayList<String>(Intern(parser.getAVars())); // Retain order given in MDP file
		_alContAllVars = new ArrayList<String>(_alContSVars);
		_alContAllVars.addAll(_alContAVars);
		//_context._hmContinuousVars = _alContAllVars;
		// Build cur-state var -> next-state var map
		_hmPrimeSubs = new HashMap<String,ArithExpr>();
		for (String var : _hsContSVars) 
			_hmPrimeSubs.put(var, new XADD.VarExpr(var + "'"));
		for (String var : _hsBoolSVars) 
			_hmPrimeSubs.put(var, new XADD.VarExpr(var + "'"));
		
		// This helper class performs the regression
		_qfunHelper = new ComputeQFunction(_context, this);
		
		// Setup a logger
		try {
			_logStream = new PrintStream(new FileOutputStream("timeSpace.txt"));//_logFileRoot + ".log"));
		} catch (FileNotFoundException e) {
			System.err.println(e);
			e.printStackTrace();
			System.exit(1);
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// Main value iteration routine
	////////////////////////////////////////////////////////////////////////////

	/**
	 * CMDP inference methods
	 **/
	public int solve(int max_iter)
	{
		//////////////////////////////////////////////////////////////////////////
		// Value iteration statistics
		_nCurIter = 0;
		if (max_iter < 0)
			max_iter = _nMaxIter;
		long[] time = new long[max_iter + 1];
		int[] num_nodes = new int[max_iter + 1]; 
		int[] num_branches = new int[max_iter + 1]; 
		//////////////////////////////////////////////////////////////////////////
		
		// Initialize value function to zero
		_valueDD = _context.getTermNode(XADD.ZERO);

		// Perform value iteration for specified number of iterations, or until convergence detected
		while (_nCurIter < max_iter) 
		{
			++_nCurIter;
			ResetTimer();
			_logStream.println("Iteration #" + _nCurIter + ", " + MemDisplay() + " bytes, " + GetElapsedTime() + " ms");
			_logStream.flush();
			
			// Prime diagram
			_prevDD = _valueDD;

			// Iterate over each action
			_maxDD = null;
			for (Map.Entry<String,CAction> me : _hmName2Action.entrySet()) {

				// Regress the current value function through each action (finite number of continuous actions)
				int regr = _qfunHelper.regress(_valueDD, me.getValue());
				regr  = _context.reduceRound(regr);
				if (DISPLAY_POSTMAX_Q);
					//doDisplay(regr, _logFileRoot + ": Q^" + _nCurIter + "(" + me.getKey() + ")");
				
				// Take the max over this action and the previous action 
				//(can have continuous parameters which represents many discrete actions)
				///////ADD THIS TO SCOTT'S CODE
				regr = _context.makeCanonical(regr);
				if (_maxDD == null)
				{
					_maxDD = regr;
					if (REDUNDANDY_CHECK)
						_maxDD = _context.reduceLP(_maxDD,true);
					else
					_maxDD = _context.reduceLP(_maxDD);

				}

				else {
					_maxDD = _context.apply(_maxDD, regr, XADD.MAX);
					_maxDD = _context.reduceLinearize(_maxDD);
					_maxDD  = _context.reduceRound(_maxDD);
					_maxDD = _context.makeCanonical(_maxDD);
					//_logStream.println("Number of nodes before reducing redundant paths: "+_context.getNodeCount(_maxDD));
					if (REDUNDANDY_CHECK)
						_maxDD = _context.reduceLP(_maxDD,true);
					else
					_maxDD = _context.reduceLP(_maxDD);
					_maxDD = _context.makeCanonical(_maxDD);
					//_logStream.println("Number of nodes after reducing redundant paths: "+_context.getNodeCount(_maxDD));
		           // if (_maxDD != _context.makeCanonical(_maxDD)) {
		            	//System.err.println("CAMDP VI ERROR: encountered non-canonical node that should have been canonical");
		            	//System.exit(1);
		           // }
				}
				if(DISPLAY_MAX)
					displayGraph(_maxDD, "max-" + _nCurIter);

				flushCaches();
			}
			//_maxDD = _context.makeCanonical(_maxDD);
			_valueDD = _maxDD;
			//_logStream.println("- V^" + _nCurIter + _context.getString(_valueDD));
			//doDisplay(_valueDD, _logFileRoot + ": V^"+_nCurIter);
			doDisplay(_valueDD, "V^"+_nCurIter+".dot");
			
			//////////////////////////////////////////////////////////////////////////
			// Value iteration statistics
			time[_nCurIter] = GetElapsedTime();
			num_nodes[_nCurIter] = _context.getNodeCount(_valueDD);
			num_branches[_nCurIter] = _context.getBranchCount(_valueDD);
			_logStream.println("Value function size @ end of iteration " + _nCurIter + 
					": " + num_nodes[_nCurIter] + " nodes = " + 
					num_branches[_nCurIter] + " cases" + " in " + time[_nCurIter] + " ms");
			//////////////////////////////////////////////////////////////////////////
		}

		flushCaches();	
		
		//////////////////////////////////////////////////////////////////////////
		// Performance Logging
		_logStream.println("\nValue iteration complete!");
		_logStream.println(max_iter + " iterations took " + GetElapsedTime() + " ms");
		_logStream.println("Canonical / non-canonical: " + XADD.OperExpr.ALREADY_CANONICAL + " / " + XADD.OperExpr.NON_CANONICAL);

		_logStream.println("\nIteration Results summary");
		for (int i = 1; i <= max_iter; i++) {
			String branch_count = num_branches[i] >= 0 
			? "" + num_branches[i] : " > " + XADD.MAX_BRANCH_COUNT; 
			_logStream.println("Iter " + i + ": nodes = " + num_nodes[i] + "\tbranches = " + branch_count + "\ttime = " + time[i] + " ms");
		}
		//////////////////////////////////////////////////////////////////////////

		return _nCurIter;
	}

	////////////////////////////////////////////////////////////////////////////
	// Miscellaneous
	////////////////////////////////////////////////////////////////////////////
	
	public void flushCaches() {
		flushCaches(new ArrayList<Integer>());
	}
	
	public void flushCaches(List<Integer> special_nodes) {
		if (((double)RUNTIME.freeMemory() / 
				(double)RUNTIME.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			System.out.println("No need to flush caches.");
			return; // Still enough free mem to exceed minimum requirements
		}
		
		// Commence cache flushing
		_logStream.println("Before flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");

		// TODO: Maybe keeping these is worthwhile?
		_hmContRegrCache.clear();
		
		_context.clearSpecialNodes();
		for (Integer node : special_nodes)
			_context.addSpecialNode(node);

		for (CAction a : _hmName2Action.values()) {
			_context.addSpecialNode(a._reward);
			for (Integer xadd : a._hmVar2DD.values())
				_context.addSpecialNode(xadd);
		}
		if (_prevDD!=null){
			_context.addSpecialNode(_prevDD);
		}
		if (_maxDD!=null){
			_context.addSpecialNode(_maxDD);
		}
		if (_valueDD!=null){
			_context.addSpecialNode(_valueDD); 
		}
		_context.flushCaches();

		_logStream.println("After flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");
	}

	public String toString() {
		return toString(false, false);
	}

	public String toString(boolean display_reward, boolean display_value) {
		StringBuffer sb = new StringBuffer();
		sb.append("\nCMDP Definition:\n===============\n");
		sb.append("CVars:       " + /*_context.getContinuousVarList() + */" / " + 
				_alContAllVars + " = " + _hsContSVars + " + " + _hsContAVars + "\n");
		sb.append("Min-values:  " + _context._hmMinVal + "\n");
		sb.append("Max-values:  " + _context._hmMaxVal + "\n");
		sb.append("BVars:       " + _context._alBooleanVars + "/" + _hsBoolSVars + "\n");
		sb.append("Order:       " + _context._alOrder + "\n");
		sb.append("Iterations:  " + _nMaxIter + "\n");
		sb.append("Constraints (" + _alConstraints.size() + "):\n");
		for (Integer cons : _alConstraints) {
			sb.append("- " + _context.getString(cons) + "\n");
		}
		sb.append("Actions (" + _hmName2Action.size() + "):\n");
		for (CAction a : _hmName2Action.values()) {
			sb.append("\n==> " + a);
		}
		sb.append("\n");

		if (display_value) {
			Graph g = _context.getGraph(_valueDD);
			//g.launchViewer(1300, 770);
		}

		return sb.toString();
	}

	public void doDisplay(int xadd_id, String label) {
		if (DISPLAY_V) 
			displayGraph(xadd_id, label);
		if (DISPLAY_2D)
			display2D(xadd_id, label);
		if (DISPLAY_3D) 
			display3D(xadd_id, label);
	}
	
	public void displayGraph(int xadd_id, String label) {
		Graph g = _context.getGraph(xadd_id);
		String[] split = label.split("[\\\\/]");
		label = split[split.length - 1];
		label = label.replace(".camdp", "").replace(".cmdp", "");
		g.addNode("_temp_");
		g.addNodeLabel("_temp_", label);
		g.addNodeShape("_temp_", "square");
		g.addNodeStyle("_temp_", "filled");
		g.addNodeColor("_temp_", "gold1");
		g.genDotFile(label);
		g.launchViewer(1300, 770);
	}

	public void display2D(int xadd_id, String label) {
		
		// If DISPLAY_2D is enabled, it is expected that necessary parameters 
		// have been placed in a _problemFile + ".2d"
		FileOptions opt = new FileOptions(_problemFile + ".2d");

		System.out.println("Plotting 2D...");
		System.out.println("var: " + opt._var.get(0) + ", [" + opt._varLB.get(0) + ", " + 
				opt._varInc.get(0) + ", " + opt._varUB.get(0) + "]");
		System.out.println("bassign: " + opt._bassign);
		System.out.println("dassign: " + opt._dassign);
		
		TestXADDDist.PlotXADD(_context, xadd_id, 
				opt._varLB.get(0), opt._varInc.get(0), opt._varUB.get(0), 
				opt._bassign, opt._dassign, opt._var.get(0), label);
	}
	
	public void display3D(int xadd_id, String label) {
		
		// If DISPLAY_3D is enabled, it is expected that necessary parameters 
		// have been placed in a _problemFile + ".2d"
		FileOptions opt = new FileOptions(_problemFile + ".3d");

		System.out.println("Plotting 3D...");
		System.out.println("var: " + opt._var.get(1) + ", [" + opt._varLB.get(1) + ", " + 
				opt._varInc.get(1) + ", " + opt._varUB.get(1) + "]");
		System.out.println("bassign: " + opt._bassign);
		System.out.println("dassign: " + opt._dassign);

		TestXADDDist.Plot3DXADD(_context, xadd_id, 
				opt._varLB.get(0), opt._varInc.get(0), opt._varUB.get(0), 
				opt._varLB.get(1), opt._varInc.get(1), opt._varUB.get(1), 
				opt._bassign, opt._dassign, opt._var.get(0), opt._var.get(1), label,_problemFile);
	}
	
	// A helper class to load options for 2D and 3D plotting for specific problems
	public class FileOptions {
		public ArrayList<String> _var = new ArrayList<String>();
		public ArrayList<Double> _varLB = new ArrayList<Double>();
		public ArrayList<Double> _varInc = new ArrayList<Double>();
		public ArrayList<Double> _varUB = new ArrayList<Double>();
		public HashMap<String,Boolean> _bassign = new HashMap<String, Boolean>();
		public HashMap<String,Double>  _dassign = new HashMap<String, Double>();
		public FileOptions(String filename) {
			String line = null;
			try {
				BufferedReader br = new BufferedReader(new FileReader(filename));
				while ((line = br.readLine()) != null) {
					line = line.trim();
					if (line.length() == 0)
						continue;
					String[] split = line.split("\t");
					String label = split[0].trim();
					if (label.equalsIgnoreCase("var")) {
						// Line format: var name lb inc ub
						_var.add(split[1].trim());
						_varLB.add(Double.parseDouble(split[2]));
						_varInc.add(Double.parseDouble(split[3]));
						_varUB.add(Double.parseDouble(split[4]));
					} else if (label.equalsIgnoreCase("bassign")) {
						// Line format: bassign name {true,false}
						_bassign.put(split[1].trim(), Boolean.parseBoolean(split[2]));
					} else if (label.equalsIgnoreCase("cassign")) {
						// Line format: cassign name double
						_dassign.put(split[1].trim(), Double.parseDouble(split[2]));
					} else {
						throw new Exception("ERROR: Unexpected line label '" + label + "', not {var, bassign, dassign}");
					}
				}
			} catch (Exception e) {
				System.err.println(e + "\nContent at current line: '" + line + "'");
				System.err.println("ERROR: could not read 2d file: " + filename + ", exiting.");
			}		
		}
	}
	
	// Reset elapsed time
	public static void ResetTimer() {
		_lTime = System.currentTimeMillis(); 
	}

	// Get the elapsed time since resetting the timer
	public static long GetElapsedTime() {
		return System.currentTimeMillis() - _lTime;
	}

	public static String MemDisplay() {
		long total = RUNTIME.totalMemory();
		long free  = RUNTIME.freeMemory();
		return total - free + ":" + total;
	}

	////////////////////////////////////////////////////////////////////////////
	// Testing Interface
	////////////////////////////////////////////////////////////////////////////
	
	public static String InsertDirectory(String filename, String add_dir) {
		try {
			File f = new File(filename);
			String parent = f.getParent();
			return (parent == null ? "" : parent) + File.separator + add_dir + 
				File.separator + f.getName();
		} catch (Exception e) {
			System.err.println("Could not insert directory '" + add_dir + "' into '" + filename + "' to produce output files.");
			System.exit(1);
		}
		return null;
	}

	public ArrayList<String> Intern(ArrayList<String> l) {
		ArrayList<String> ret = new ArrayList<String>();
		for (String s : l)
			ret.add(s.intern());
		return ret;
	}
	
	public static void Usage() {
		System.out.println("\nUsage: MDP-filename #iter display-2D? display-3D?");
		System.exit(1);
	}

	public static void main(String args[]) {
		if (args.length != 4) {
			Usage();
		}

		// Parse problem filename
		String filename = args[0];

		// Parse iterations
		int iter = -1;
		try {
			iter = Integer.parseInt(args[1]);
		} catch (NumberFormatException nfe) {
			System.out.println("\nIllegal iteration value\n");
			Usage();
		}

		// Build a CAMDP, display, solve
		CAMDP mdp = new CAMDP(filename);
		mdp.DISPLAY_2D = Boolean.parseBoolean(args[2]);
		mdp.DISPLAY_3D = Boolean.parseBoolean(args[3]);
		System.out.println(mdp.toString(false, false));
		//System.in.read();

		int iter_used = mdp.solve(iter);
		System.out.println("\nSolution complete, required " + 
				iter_used + " / " + iter + " iterations.");
		
		//System.err.println("\n\nIMPLICATIONS:\n" + mdp._context.showImplications());
	}
}
