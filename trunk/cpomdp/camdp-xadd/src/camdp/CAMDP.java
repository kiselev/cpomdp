// Package definition
package camdp;

// Packages to import
import graph.Graph;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.AnnotatedElement;
import java.math.BigDecimal;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import java_cup.parser;

import util.IntTriple;
import xadd.TestXADDDist;
import xadd.XADD;
import xadd.XADD.ArithExpr;
import xadd.XADD.XADDNode;
import xadd.XADD.XADDTNode;
import cmdp.HierarchicalParser;

/**
 * Main CAMDP inference class
 * Class for continuous states and actions
 * Exact solution to the value function considering the maximum points of the Q-function defined by the actions
 * Partitions according to both the state and the action
 * 
 * @version 1.0
 * @author Zahra
 * @language Java (JDK 1.5)
 **/
public class CAMDP {

	/* Constants */
	public final static boolean REDUCE_LP = true;

	public final static boolean DISPLAY_Q = false;
	public final static boolean DISPLAY_V = true;
	public final static boolean DISPLAY_2D = false;
	public final static boolean DISPLAY_MAX = false;
	public final static boolean DISPLAY_POLICY = false;
	public final static boolean PRINTSCREENEVAL = false;
	public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < amt

	public static boolean PRINT3DFILE=false;
	public static String varX;
	public static String varY;
	public static boolean rover=false;
	public static double size3D = 10d; // Won't flush until < amt
	public final static ArrayList<String> ZERO  =  new ArrayList<String> (Arrays.asList("[0]"));  
	/* For printing */
	public static DecimalFormat _df = new DecimalFormat("#.###");
	//public static String  NAME_FILE_3D = ""; //"src/camdp/ex/data";
	public static PrintStream os;
	/* Static variables */
	public static long _lTime; // For timing purposes
	public static Runtime RUNTIME = Runtime.getRuntime();


	/* Local vars */
	public XADD _context = null;
	public ArrayList<String> contVars;

	public Integer _valueDD; // The resulting value function once this CMDP has
	// been solved
	public Integer _maxDD;
	public Integer _prevDD;
	public BigDecimal _bdDiscount;   // Discount (gamma) for CMDP
	public Integer    _nIter; // Tolerance (gamma) for CMDP

	public HashMap<String,CAction> _hmName2Action;
	public ArrayList<Integer> _alConstraints;

	public HashMap<IntTriple,Integer> _hmRegrKey2Node;

	////////////////////////////////////////////////////////////////////////////
	// Constructors
	////////////////////////////////////////////////////////////////////////////

	/**
	 * Constructor - filename
	 **/
	public CAMDP(String filename) {
		this(HierarchicalParser.ParseFile(filename));
		//don't give address because of server
		//NAME_FILE_3D= filename.substring(13,filename.indexOf("."))+".dat";
		//NAME_FILE_3D = NAME_FILE_3D.toLowerCase();
		//if (NAME_FILE_3D.contains("rover")) rover = true;
		//NAME_FILE_3D = filename+ ".dat";
		try {
			//String timefile = FILE_TIME_MEM+filename.substring(12,filename.indexOf("."))+".txt";
			String timefile=  "timeSpace.txt";
			os = new PrintStream(new FileOutputStream(timefile));
		} catch (IOException e) {
			System.err.println(e);
		}
	}

	/**
	 * Constructor - pre-parsed file
	 **/
	public CAMDP(ArrayList input) {
		_context = new XADD();
		_prevDD = _maxDD = _valueDD = null;
		_bdDiscount = new BigDecimal("" + (-1));
		_nIter = null;
		_hmName2Action = new HashMap<String,CAction>();
		_hmRegrKey2Node = new HashMap<IntTriple,Integer>();

		ParseCAMDP parser = new ParseCAMDP(this);
		parser.buildCAMDP(input);
		_context._hmMaxVal=parser._maxCVal;
		_context._hmMinVal = parser._minCVal;
		_context._hsBooleanVars = parser.getBVars();
		_alConstraints = parser.getConstraints();
		_nIter = parser.getIterations();
		_bdDiscount = parser.getDiscount();
		_hmName2Action = parser.getHashmap();
		contVars = new ArrayList<String>();
		contVars.addAll(parser.getCVars());
		contVars.addAll(parser.getAVars());
		_context._hmContinuousVars = contVars;
	}

	/**
	 * CMDP inference methods
	 **/
	public int solve(int max_iter)
	{
		// Set value function equal to zero
		_valueDD =_context.buildCanonicalXADD(ZERO);
		//value function does not have any actions in it: 
		/*ArrayList l0 =new ArrayList();
		l0.add("[-50 + x2*1 >=0]");
		ArrayList l0t = new ArrayList();
		ArrayList l0f = new ArrayList();
		l0t.add("0");
		l0f.add("-100");
		l0.add(l0t);
		l0.add(l0f);
		
		ArrayList l1 =new ArrayList();
		l1.add("[-50 + x1*1 >=0]");
		ArrayList l1f = new ArrayList();
		l1f.add("-200");
		l1.add(l0);
		l1.add(l1f);
		
		ArrayList l2 = new ArrayList();
		l2.add("[-4500 + x2 <=0]");
		ArrayList l2f = new ArrayList();
		l2f.add("-100");
		l2.add(l1);
		l2.add(l2f);
		
		ArrayList l3 = new ArrayList();
		l3.add("[-4500 + x1 <=0]");
		ArrayList l3f = new ArrayList();
		l3f.add("-100");
		l3.add(l2);
		l3.add(l3f);
		_valueDD =_context.buildCanonicalXADD(l3);*/
		
		Paint3D paint = new Paint3D(this);
		int iter = 0;
		long[] time = new long[max_iter + 1];
		int[] num_nodes = new int[max_iter + 1]; 
		int[] num_branches = new int[max_iter + 1]; 
		double[] num_cases = new double[max_iter + 1]; 
		for (int i = 0; i <= max_iter; i++)
			num_cases[i] = 1;

		if (max_iter < 0)
			max_iter = _nIter;
		
		while (++iter <= max_iter) 
		{
			ResetTimer();
			//System.out.println("Iteration #" + iter + ", " + MemDisplay()
			//		+ " bytes, " + GetElapsedTime() + " ms");
			os.println("Iteration #" + iter + ", " + MemDisplay()
							+ " bytes, " + GetElapsedTime() + " ms");
			os.flush();
			// Prime diagram
			_prevDD = _valueDD;

			// Iterate over each action
			_maxDD=null;
			for (Map.Entry<String,CAction> me : _hmName2Action.entrySet()) 
			{
				// Regress the current value function through each action (finite number of continuous actions)
				if (_context.ANNOTATE_ENABLE)
					_valueDD = _context.annotateXADD(_valueDD, _context.getTermNode(ArithExpr.parse("0"),ArithExpr.parse("0")));
				ComputeVfunction computation = new ComputeVfunction(_context,this);
				int regr = computation.computeValueFunction(_valueDD, me.getValue());
				_context = computation.getXadd();
				_hmRegrKey2Node = computation.getHashReg();
				
				regr  = _context.reduceRound(regr);
				if (REDUCE_LP) {
					regr = _context.reduceLP(regr, contVars);
				}
				//this is like an append! 
				if (_context.ANNOTATE_ENABLE)
					regr = _context.annotateXADD(regr,me.getKey());
				if (DISPLAY_Q) {
					Graph g = _context.getGraph(regr);
					g.addNode("_temp_");
					g.addNodeLabel("_temp_", "Q^" + iter + "(" + me.getKey() + ")");
					g.addNodeShape("_temp_", "square");
					g.addNodeStyle("_temp_", "filled");
					g.addNodeColor("_temp_", "lightblue");
					g.launchViewer(1300, 770);
					
					if(PRINT3DFILE){
						//System.out.print("Creating data file... ");
						paint.create3DQDataFile(regr,"x1","x2","Q-"+me.getKey()+iter+".txt"); //for refinement
						//paint.create3DDataFile(_valueDD,"l1","l2"); //for refinement
						//System.out.println("done.");
					}
				}

				// Estimating number of cases
				double num_cases_in_regr = num_cases[iter - 1];
				for (Map.Entry<String,Integer> me2 : me.getValue()._hmVar2DD.entrySet()) {
					num_cases_in_regr *= _context.getBranchCount(me2.getValue()); // From regr
					if (_context._hsBooleanVars.contains(me2.getKey()) && num_cases_in_regr > 1)
						num_cases_in_regr /= 2; // Sum out a variable
				}
				num_cases_in_regr *= _context.getBranchCount( me.getValue()._reward);
				num_cases[iter] *= num_cases_in_regr; // From max
				
				// Take the max over this action and the previous action 
				//(can have continuous parameters which represents many discrete actions)
				_context.setMAX_Q(true);
				_maxDD = ((_maxDD == null) ? regr : _context.apply(_maxDD, regr, XADD.MAX,-1));
				_context.setMAX_Q(false);
				if (REDUCE_LP) {
					_maxDD = _context.reduceLP(_maxDD, contVars);
				}

				if(DISPLAY_MAX){
					Graph g = _context.getGraph(_maxDD);
					g.addNode("_temp_");
					g.addNodeLabel("_temp_", "max-" + iter);
					g.addNodeShape("_temp_", "square");
					g.addNodeStyle("_temp_", "filled");
					g.addNodeColor("_temp_", "lightblue");
					g.launchViewer(1300, 770);
					
					
				}
				flushCaches();
				if (_context.ANNOTATE_ENABLE)
					clearPolicy(_maxDD);
			}

			if (REDUCE_LP) {
				_maxDD = _context.reduceLP(_maxDD , contVars);
			}

			_valueDD = _maxDD;
			time[iter] = GetElapsedTime();
			num_nodes[iter] = _context.getNodeCount(_valueDD);
			num_branches[iter] = _context.getBranchCount(_valueDD);
			os.println("Value function size @ end of iteration " + iter + 
					": " + num_nodes[iter] + " nodes = " + 
					num_branches[iter] + " cases" + " in " + time[iter] + " ms");
			/*System.out.println("Value function size @ end of iteration " + iter + 
					": " + num_nodes[iter] + " nodes = " + 
					num_branches[iter] + " cases" + " in " + time[iter] + " ms");*/

			if (DISPLAY_V) 
			{
				//System.out.print("Displaying value function... ");
				Graph g = _context.getGraph(_valueDD);
				g.addNode("_temp_");
				g.addNodeLabel("_temp_", "V^" + iter);
				g.addNodeShape("_temp_", "square");
				g.addNodeStyle("_temp_", "filled");
				g.addNodeColor("_temp_", "lightblue");
				g.genDotFile("V"+iter+".dot");
				
				g.launchViewer(1300, 770);
			}
			
			if (DISPLAY_POLICY)
			{
				paint.create3DPolicyFile(_valueDD,"x1","x2"); //for refinement
			}
			if (DISPLAY_2D)/*||(iter==3)*/
			{
				TestXADDDist plot = new TestXADDDist();
				HashMap<String,Boolean> bvars = new HashMap<String, Boolean>();
				HashMap<String,Double> dvars = new HashMap<String, Double>();
				if (_context._hsBooleanVars.size()>0) bvars.put(_context._hsBooleanVars.get(0), false);
				if (rover)
					plot.PlotXADD(_context, _valueDD, -40.0, 0.1, 40.0, bvars,dvars, "x", "V^"+iter);
				else 
				plot.PlotXADD(_context, _valueDD, _context._hmMinVal.get("x1"), 1, _context._hmMaxVal.get("x1"), bvars,dvars, "x1", "V^"+iter);
				//plot.Plot3DXADD(_context, _valueDD, -20, 1, 20, -30, 1, 30, bvars,dvars ,"x", "a", "V^"+iter);
				
				
			}
			//print 3d for each iteration( file outputs)
			if(PRINT3DFILE){
				//System.out.print("Creating data file... ");
				paint.create3DDataFile(_valueDD,"x1","x2"); //for refinement
				//paint.create3DDataFile(_valueDD,"l1","l2"); //for refinement
				//System.out.println("done.");
			}
			if (_context.ANNOTATE_ENABLE)
				clearPolicy();

		}
		//or just print once outside iteration
		/*if(PRINT3DFILE){
			System.out.print("Creating data file... ");
			Paint3D paint = new Paint3D(this,_context);
			//paint.create3DDataFile(_valueDD,"l1","l2"); 
			paint.create3DDataFile(_valueDD,"x1","x2"); 
			System.out.println("done.");
		}*/

		flushCaches();	

		/*//instead of print in out, print to file
		 * System.out.println("\nValue iteration complete!");
		System.out.println(max_iter + " iterations took " + GetElapsedTime() + " ms");
		System.out.println("Canonical / non-canonical: " + XADD.OperExpr.ALREADY_CANONICAL + " / " + XADD.OperExpr.NON_CANONICAL);

		os.println("\nIteration Results summary");
		for (int i = 1; i <= max_iter; i++) {
			String branch_count = num_branches[i] >= 0 
			? "" + num_branches[i]
			                    : " > " + XADD.MAX_BRANCH_COUNT; 
			System.out.println("Iter " + i + ": nodes = " + num_nodes[i] + "\tbranches = " + branch_count + "\tcases = " + num_cases[i] + "\ttime = " + time[i] + " ms");
		}*/
		
		
		os.println("\nValue iteration complete!");
		os.println(max_iter + " iterations took " + GetElapsedTime() + " ms");
		os.println("Canonical / non-canonical: " + XADD.OperExpr.ALREADY_CANONICAL + " / " + XADD.OperExpr.NON_CANONICAL);

		os.println("\nIteration Results summary");
		for (int i = 1; i <= max_iter; i++) {
			String branch_count = num_branches[i] >= 0 
			? "" + num_branches[i]
			                    : " > " + XADD.MAX_BRANCH_COUNT; 
			os.println("Iter " + i + ": nodes = " + num_nodes[i] + "\tbranches = " + branch_count + "\tcases = " + num_cases[i] + "\ttime = " + time[i] + " ms");
		}

		return iter;
	}


	private void clearPolicy() {
		/*for (int i=1;i<_context._hmNode2Int.size();i++)
			_context.annotateXADD(i, null);*/
		for (Integer node : _context._hsSpecialNodes)//or null
			_context.annotateXADD(node,_context.getTermNode(ArithExpr.parse("0"),ArithExpr.parse("0")));
		
	}
	private void clearPolicy(int max_dd) {
		/*for (int i=1;i<_context._hmNode2Int.size();i++)
			_context.annotateXADD(i, null);*/
		for (Integer node : _context._hsSpecialNodes)//or null
			if (node!=max_dd)
			_context.annotateXADD(node,_context.getTermNode(ArithExpr.parse("0"),ArithExpr.parse("0")));
		
	}

	////////////////////////////////////////////////////////////////////////////
	// Miscellaneous
	////////////////////////////////////////////////////////////////////////////
	public void flushCaches() {
		flushCaches(new ArrayList<Integer>());
	}
	
	public void flushCaches(ArrayList<Integer> special_nodes) {
		if (!_context.ANNOTATE_ENABLE)
		{
			if (((double)RUNTIME.freeMemory() / 
				(double)RUNTIME.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			//System.out.println("No need to flush caches.");
			return; // Still enough free mem to exceed minimum requirements
			}
			os.println("Before flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");
		}
		/*System.out.println("Before flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");*/
		 
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

		_hmRegrKey2Node.clear();

		/*System.out.println("After flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");
		*/
		os.println("After flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " + 
				_df.format(RUNTIME.freeMemory()/10e6d) + " MB = " + 
				_df.format(100d*RUNTIME.freeMemory()/(double)RUNTIME.totalMemory()) + "% available memory");
	
	
	}



	public String toString() {
		return toString(false, false);
	}

	public String toString(boolean display_reward, boolean display_value) {
		StringBuffer sb = new StringBuffer();
		sb.append("\nCMDP Definition:\n===============\n");
		sb.append("CVars:       " + _context._hmContinuousVars + "\n");
		sb.append("Min-values:  " + _context._hmMinVal + "\n");
		sb.append("Max-values:  " + _context._hmMaxVal + "\n");
		sb.append("BVars:       " + _context._hsBooleanVars + "\n");
		sb.append("Order:       " + _context._alOrder + "\n");
		sb.append("Iterations:  " + _nIter + "\n");
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

	// Reset elapsed time
	public void ResetTimer() {
		_lTime = System.currentTimeMillis(); 
	}

	// Get the elapsed time since resetting the timer
	public long GetElapsedTime() {
		return System.currentTimeMillis() - _lTime;
	}

	public static String MemDisplay() {
		long total = RUNTIME.totalMemory();
		long free = RUNTIME.freeMemory();
		return total - free + ":" + total;
	}

	
////////////////////////////////
	//Getters and setters

	

	public BigDecimal get_bdDiscount() {
		return _bdDiscount;
	}

	public void set_bdDiscount(BigDecimal _bdDiscount) {
		this._bdDiscount = _bdDiscount;
	}

	public ArrayList<Integer> get_alConstraints() {
		return _alConstraints;
	}

	public void set_alConstraints(ArrayList<Integer> _alConstraints) {
		this._alConstraints = _alConstraints;
	}

	public HashMap<IntTriple, Integer> get_hmRegrKey2Node() {
		return _hmRegrKey2Node;
	}

	public void set_hmRegrKey2Node(HashMap<IntTriple, Integer> _hmRegrKey2Node) {
		this._hmRegrKey2Node = _hmRegrKey2Node;
	}


	////////////////////////////////////////////////////////////////////////////
	// Testing Interface
	////////////////////////////////////////////////////////////////////////////

	public static void usage() {
		System.out.println("\nMust enter: MDP-filename");
		System.out.println("\nMust enter: number of iterations");
		System.out.println("\nMust enter: print 3D file?");

		System.exit(1);
	}

	public static void main(String args[]) {
		if (args.length < 2 || args.length > 7) {
			usage();
		}

		// Parse problem filename
		String filename = args[0];

		// Parse iterations
		int iter = -1;
		try {
			iter = Integer.parseInt(args[1]);
		} catch (NumberFormatException nfe) {
			System.out.println("\nIllegal iteration value\n");
			System.exit(1);
		}
		catch(ArrayIndexOutOfBoundsException aiobe){
			System.out.println("\nIMissing argument\n");
			usage();
		}

		try {
			if (args.length >= 3)
				PRINT3DFILE = Boolean.parseBoolean(args[2]);
		} catch (NumberFormatException nfe) {
			System.out.println("\nIllegal print3DFile value: "+ args[2] + "\n");
			System.exit(1);
		}

		// Build a CMDP, display, solve
		CAMDP mdp1 = new CAMDP(filename);
		//System.out.println(mdp1.toString(false, false));
		//System.exit(1);

		int  iter1 = mdp1.solve(iter);
		long time1 = mdp1.GetElapsedTime();
	}



}
