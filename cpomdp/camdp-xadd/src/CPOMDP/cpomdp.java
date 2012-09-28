package CPOMDP;

import graph.Graph;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.math.BigDecimal;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import CPOMDP.contObs.ContComputeGamma;
import CPOMDP.contObs.ContParsePOMDP;

import camdp.CAMDP;
import camdp.CAction;
import camdp.ParseCAMDP;
import cmdp.HierarchicalParser;
import util.IntTriple;
import xadd.TestXADDDist;
import xadd.XADD;
import xadd.XADD.ArithExpr;
import xadd.XADD.DoubleExpr;
import xadd.XADD.XADDTNode;

public class cpomdp {

	/* Constants */
	public final static String RESULTS_DIR = "results"; // Diagnostic output destination
	public final static boolean DISPLAY_V = true;
	public final static boolean DISPLAY_G = true;
	/* Maintain an explicit policy? */
	public final static boolean MAINTAIN_POLICY = false;

	/* Cache maintenance */
	public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < amt

	/* For printing */
	public static DecimalFormat _df = new DecimalFormat("#.###");
	public static PrintStream _logStream = null;
	public static int filecounter = 0;
	/* Static variables */
	public static long _lTime; // For timing purposes
	public static Runtime RUNTIME = Runtime.getRuntime();

	/* Local vars */
	public boolean DISPLAY_2D = false;
	public boolean DISPLAY_3D = true;

	public String _problemFile = null;
	public String _logFileRoot = null;
	public XADD _context = null;
	public HashSet<String> _hsBoolSVars;
	public HashSet<String> _hsBoolOVars;
	public HashSet<String> _hsContSVars;
	public HashSet<String> _hsContOVars;

	public ArrayList<String> _alBoolSVars; // Retain order given in MDP file
	public ArrayList<String> _alBoolOVars; // Retain order given in MDP file
	public ArrayList<String> _alContSVars; // Retain order given in MDP file
	public ArrayList<String> _alContOVars; // Retain order given in MDP file
	public ArrayList<String> _alContAllVars; //state and observation

	public Integer _valueDD; // The resulting value function once this CMDP has
	public Integer _maxDD;
	public Integer _prevDD;
	public BigDecimal _bdDiscount; // Discount (gamma) for CMDP
	public Integer    _nMaxIter;   // Number of iterations for CMDP
	public Integer    _nCurIter;   // Number of iterations for CMDP

	public HashMap<String,ArithExpr>  _hmPrimeSubs;
	public HashMap<String,COAction>    _hmName2Action;
	public HashMap<IntTriple,Integer> _hmContRegrCache;
	public ArrayList<Integer>         _alConstraints;
	
	//public ComputeGamma _gammaHelper = null;
	//public DiscreteObsGamma _gammaHelper = null;
	public ContComputeGamma _gammaHelper = null;
	public HashMap<Integer,Integer> _currentgammaSet_h;
	public HashMap<Integer,Integer> _previousgammaSet_h;
	public HashMap<Integer,PartitionObsState> _obspartitions= new HashMap<Integer,PartitionObsState>();
	int[] belief = new int[2];
	int[] beliefBasedVectors = new int[2];
	public cpomdp(String filename) {
		this(filename, HierarchicalParser.ParseFile(filename));
	}

	public cpomdp(String file_source, ArrayList input) {

		// Basic initializations
		_problemFile = file_source;
		_logFileRoot = InsertDirectory(_problemFile, RESULTS_DIR).replace("-", "_");
		_context = new XADD();
		_prevDD = _maxDD = _valueDD = null;
		_bdDiscount = new BigDecimal("" + (-1));
		_nMaxIter = null;
		// Setup CAMDP according to parsed file contents
		ContParsePOMDP parser = new ContParsePOMDP(this);
		// ParsePOMDP parser = new ParsePOMDP(this);
		parser.buildPOMDP(input);
		_context._hmMaxVal = parser._maxCVal;
		_context._hmMinVal = parser._minCVal;
		_context._hsBooleanVars = parser.getBVars();
		
		_alConstraints = parser.getConstraints();
		_nMaxIter = parser.getIterations();
		_bdDiscount = parser.getDiscount();
		_hmName2Action = parser.getHashmap();
		_hmContRegrCache = new HashMap<IntTriple,Integer>();

		// Setup variable sets and lists
		_hsBoolSVars = new HashSet<String>(Intern(parser.getBVars()));
		_hsBoolOVars = new HashSet<String>(Intern(parser.getBOVars()));
		_hsContSVars = new HashSet<String>(Intern(parser.getCVars()));
		_hsContOVars = new HashSet<String>(Intern(parser.getOVars()));
		_alBoolSVars = new ArrayList<String>(Intern(parser.getBVars())); // Retain order given in MDP file
		_alBoolOVars = new ArrayList<String>(Intern(parser.getBOVars())); // Retain order given in MDP file
		_alContSVars = new ArrayList<String>(Intern(parser.getCVars())); // Retain order given in MDP file
		_alContOVars = new ArrayList<String>(Intern(parser.getOVars())); // Retain order given in MDP file
		_alContAllVars = new ArrayList<String>(_alContSVars);
		_alContAllVars.addAll(_alContOVars);
		//_context._hmContinuousVars = _alContAllVars;

		
		
		//_gammaHelper = new ComputeGamma(_context, this);
		//_gammaHelper = new DiscreteObsGamma(_context, this);
		_gammaHelper = new ContComputeGamma(_context, this);
		_previousgammaSet_h = new HashMap<Integer, Integer>();
		_currentgammaSet_h = new HashMap<Integer, Integer>();
		// Build cur-state var -> next-state var map
		_hmPrimeSubs = new HashMap<String,ArithExpr>();
		for (String var : _hsContSVars) 
			_hmPrimeSubs.put(var, new XADD.VarExpr(var + "'"));
		for (String var : _hsBoolSVars) 
			_hmPrimeSubs.put(var, new XADD.VarExpr(var + "'"));

		// Perform progression and regression?

		// Setup a logger
		try {
			_logStream = new PrintStream(new FileOutputStream(_logFileRoot + ".log"));
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
		//define belief: 
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
				
				ArrayList l1 =new ArrayList();
				l1.add("[-11 + t*1 <= 0]");
				ArrayList l1t = new ArrayList();
				ArrayList l1f = new ArrayList();
				l1t.add("[-6 + t*1 >= 0]");
				ArrayList l1tt = new ArrayList();
				ArrayList l1tf = new ArrayList();
				l1tt.add("0.2");
				l1tf.add("0");
				l1t.add(l1tt);
				l1t.add(l1tf);
				l1f.add("0");
				l1.add(l1t);
				l1.add(l1f);
				
				
				//for 2d:
		/*		ArrayList l1 =new ArrayList();
				l0.add("[-10 + p*1 <= 0]");
				ArrayList l0t = new ArrayList();
				ArrayList l0f = new ArrayList();
				l0t.add("[p*1 >= 0]");
				ArrayList l0tt = new ArrayList();
				ArrayList l0tf = new ArrayList();
				l0tt.add("[-100 + t*1 <= 0]");
				ArrayList l0ttt = new ArrayList();
				ArrayList l0ttf = new ArrayList();
				l0ttt.add("[ -90 + t*1 >= 0]");
				ArrayList l0tttt = new ArrayList();
				ArrayList l0tttf = new ArrayList();
				l0tttt.add("0.01");
				l0tttf.add("0");
				l0ttt.add(l0tttt);
				l0ttt.add(l0tttf);
				l0ttf.add("0");
				l0tt.add(l0ttt);
				l0tt.add(l0ttf);
				l0tf.add("0");
				l0t.add(l0tt);
				l0t.add(l0tf);
				l0f.add("0");
				l0.add(l0t);
				l0.add(l0f);
				
				l1.add("[-30 + p*1 <= 0]");
				ArrayList l1t = new ArrayList();
				ArrayList l1f = new ArrayList();
				l1t.add("[-10 + p*1 >= 0]");
				ArrayList l1tt = new ArrayList();
				ArrayList l1tf = new ArrayList();
				l1tt.add("[-130 + t*1 <= 0]");
				ArrayList l1ttt = new ArrayList();
				ArrayList l1ttf = new ArrayList();
				l1ttt.add("[-90 + t*1 >= 0]");
				ArrayList l1tttt = new ArrayList();
				ArrayList l1tttf = new ArrayList();
				l1tttt.add("0.00125");
				l1tttf.add("0");
				l1ttt.add(l1tttt);
				l1ttt.add(l1tttf);
				l1ttf.add("0");
				l1tt.add(l1ttt);
				l1tt.add(l1ttf);
				l1tf.add("0");
				l1t.add(l1tt);
				l1t.add(l1tf);
				l1f.add("0");
				l1.add(l1t);
				l1.add(l1f);*/
				
				int b0 = _context.buildCanonicalXADD(l0);
				belief[0] = b0;
				int b1 = _context.buildCanonicalXADD(l1);
				belief[1] = b1;
		
		
		///////////////////////////////////////////////////////////////////////
		// Initialize value function to zero
		//_currentgammaSet_h.put(0,_context.getTermNode(XADD.NEG_ONE));
		//for 2D
		_currentgammaSet_h.put(0,_context.getTermNode(XADD.ZERO));
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
			_previousgammaSet_h = _currentgammaSet_h;
			_currentgammaSet_h = new HashMap<Integer, Integer>();

			
			//for every belief find the maximum alpha  vector
			for (int i=0;i<belief.length;i++)
			{
				// Iterate over each action
				int counter=0;
				_maxDD = null;
				for (Map.Entry<String,COAction> me : _hmName2Action.entrySet()) 
				{

					//counter++;
					//a test alpha in the set
					/*ArrayList l0 =new ArrayList();
					l0.add("[-10 + t*1 >=0]");
					ArrayList l0t = new ArrayList();
					ArrayList l0f = new ArrayList();
					l0t.add("-1000");
					l0f.add("100");
					l0.add(l0t);
					l0.add(l0f);
					int alpha = _context.buildCanonicalXADD(l0);
					_previousgammaSet_h.put(1, alpha);*/
					
					int[] regr = _gammaHelper.computeGamma(me.getValue(),_previousgammaSet_h,belief[i]);
					//the result is Gamma^h_a, add this to the current set of Gamma^h_a
					
					for (int j=0;j<regr.length;j++)
					{
						_currentgammaSet_h.put(counter++, regr[j]);
						//doDisplay(regr[j], ": alpha_vector"+(j+1)+"for action: "+ me.getValue()._sName);
					}
				
					//flushCaches();
				}

				//pruning the _alpha vectors
			//	_currentgammaSet_h = dominanceTest(_currentgammaSet_h);
				
				_logStream.println("Number of Alpha vectors after pruning for belief "+ (i+1) + "is : " + _currentgammaSet_h.size());
				//now for this belief, compute the alpha vector that will result in the maximum value
				int alphaValue[] = new int[_currentgammaSet_h.size()];
				double maximumAlpha = 0;
				int maximumVector = 0;
				for (int j=0;j<_currentgammaSet_h.size();j++)
				{
					if (_currentgammaSet_h.get(j)!=null)
					{
						int previousS = 0;
						for (int k=0;k<_alContSVars.size();k++)
						{
							if (previousS>0)
								alphaValue[j] = _context.computeDefiniteIntegral(previousS,_alContSVars.get(k));
							else 
								{
								int r = _context.apply(_currentgammaSet_h.get(j), belief[i], _context.PROD);
								alphaValue[j] = _context.computeDefiniteIntegral(r,_alContSVars.get(k));
								}
							previousS = alphaValue[j];
						}
							XADDTNode t = (XADDTNode) _context.getNode(alphaValue[j]);
							if (j==0)
							{
								maximumAlpha = ((DoubleExpr) t._expr)._dConstVal;
								maximumVector = _currentgammaSet_h.get(j);
							}
							else if ((((DoubleExpr) t._expr)._dConstVal) > maximumAlpha) 
							{
								maximumAlpha = ((DoubleExpr) t._expr)._dConstVal;
								maximumVector = _currentgammaSet_h.get(j);
							}
						}
					}
				
				//now found the maximum alpha-vector, remove all other vectors and put this vector in the currentAlpha-set
				_currentgammaSet_h.clear();
				beliefBasedVectors[i] =  maximumVector;
					
			}
			_currentgammaSet_h.clear();
			for (int j=0;j<beliefBasedVectors.length;j++)
			{
				_currentgammaSet_h.put(j, beliefBasedVectors[j]);
				doDisplay(_currentgammaSet_h.get(j), "Iteration:" + _nCurIter+"Alpha_vector for belief"+(j+1));
				//create3DDataFile(_currentgammaSet_h.get(j),"t","p"); //for refinement

			}
			//_logStream.println("- V^" + _nCurIter + _context.getString(_valueDD));
			//doDisplay(_valueDD, _logFileRoot + ": V^"+_nCurIter);
			
			//////////////////////////////////////////////////////////////////////////
			// Value iteration statistics
			time[_nCurIter] = GetElapsedTime();
			num_nodes[_nCurIter] = _context.getNodeCount(_currentgammaSet_h.get(0))+_context.getNodeCount(_currentgammaSet_h.get(1));
			num_branches[_nCurIter] = _context.getBranchCount(_currentgammaSet_h.get(0))+_context.getNodeCount(_currentgammaSet_h.get(1));
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
	
	
	private HashMap<Integer, Integer> dominanceTest(HashMap<Integer, Integer> _currentgammaSet_h2) {
		for (int i=0;i<_currentgammaSet_h2.size();i++)
		{
			for (int j=0;j<_currentgammaSet_h2.size();j++)
			{
				if ((i!=j)&&(_currentgammaSet_h2.get(i)!=null)&&(_currentgammaSet_h2.get(j)!=null))
				{
					int result = _context.apply(_currentgammaSet_h2.get(i), _currentgammaSet_h2.get(j), _context.MAX);
					//result = _context.reduceLP(result,_alContSVars );
					if (result == _currentgammaSet_h2.get(i))
						_currentgammaSet_h2.remove(j);
					else if (result == _currentgammaSet_h2.get(j))
						_currentgammaSet_h2.remove(i);
				}
			}
		}
		return _currentgammaSet_h2;
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

		for (COAction a : _hmName2Action.values()) {
			_context.addSpecialNode(a._reward);
			for (Integer xadd : a._hmVar2DD.values())
				_context.addSpecialNode(xadd);
			for (Integer xadd : a._hmObs2DD.values())
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
		for (int i=0;i<belief.length;i++)
			_context.addSpecialNode(belief[i]);
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
		sb.append("CVars:       " +	_alContAllVars + " = " + _hsContSVars + " + " + _hsContOVars + "\n");
		sb.append("Min-values:  " + _context._hmMinVal + "\n");
		sb.append("Max-values:  " + _context._hmMaxVal + "\n");
		sb.append("BVars:       " + _context._hsBooleanVars + "/" + _hsBoolSVars + "\n");
		sb.append("BOVars:       " + _hsBoolOVars + "\n");
		sb.append("OVars:       " + _hsContOVars + "\n");
		sb.append("Order:       " + _context._alOrder + "\n");
		sb.append("Iterations:  " + _nMaxIter + "\n");
		sb.append("Constraints (" + _alConstraints.size() + "):\n");
		for (Integer cons : _alConstraints) {
			sb.append("- " + _context.getString(cons) + "\n");
		}
		sb.append("Actions (" + _hmName2Action.size() + "):\n");
		for (COAction a : _hmName2Action.values()) {
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
		g.launchViewer(1300, 770);
		//g.genDotFile("V"+iter+".dot");
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
		/*TestXADDDist.Plot3DXADD(_context, xadd_id, 
				70,10,140, 
				0,5,40, 
				opt._bassign, opt._dassign, "t", "p", "alpha_values");*/
		
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
	
	public void create3DDataFile(Integer XDD, String xVar, String yVar) {
		try {
     		filecounter++;
            BufferedWriter out = new BufferedWriter(new FileWriter("plant2d"+filecounter+".txt"));
            
            HashMap<String,Boolean> bool_assign = new HashMap<String,Boolean>();
            	
            for (String var : _context._hsBooleanVars) {
       		   bool_assign.put(var, false);	
       		}
             //values in order for rover, refinement,inventory
            Double minX,minY,maxX,maxY;
            Double size3D = 20.0;
             minX= 70.0;//_camdp._context._hmMinVal.get(xVar);
             maxX= 120.0;//_camdp._context._hmMaxVal.get(xVar);
             minY= 0.0;//_camdp._context._hmMinVal.get(yVar);
             maxY= 40.0;//_camdp._context._hmMaxVal.get(yVar);
             
             Double incX= (maxX-minX)/(size3D-1);
             Double incY= (maxY-minY)/(size3D-1);
             
             
            ArrayList<Double> X = new ArrayList<Double>();
            ArrayList<Double> Y = new ArrayList<Double>();
            

             Double xval=minX;
             Double yval=minY;
             for(int i=0;i<size3D;i++)
             {
            	 X.add(xval);
            	 Y.add(yval);
            	 xval=xval+incX;
            	 yval=yval+incY;
             }
            // System.out.println(">> Evaluations");
             for(int i=0;i<size3D;i++){
                 /*out.append(X.get(i).toString()+" ");
                 out.append(Y.get(i).toString()+" ");*/
                 for(int j=0;j<size3D;j++){
                	 
             
  		     		HashMap<String,Double> cont_assign = new HashMap<String,Double>();
  		     		
  		     		for (Map.Entry<String,Double> me : _context._hmMinVal.entrySet()) {
  		     			cont_assign.put(me.getKey(),  me.getValue());
  		     		}
  		     			     		
              		cont_assign.put(xVar,  X.get(j));
              		cont_assign.put(yVar,  Y.get(i));
              		
              		Double z=_context.evaluate(XDD, bool_assign, cont_assign);
              		
             		out.append(z.toString()+" ");
                   /*
             		cont_assign.put(xVar,  200.0d/3.0d);
              		cont_assign.put(yVar,  100.0d/3.0d);
              		z=_context.evaluate(XDD, bool_assign, cont_assign);
             		System.out.println("Eval: [" + bool_assign + "], [" + cont_assign + "]"
             						   + ": " + z);		

             		out.append(z.toString()+" ");
              		*/
              		
             		
                 }
                 out.newLine();
             }
            //out.append(System.getProperty("line.separator"));
             out.close();
             
             
             
         } catch (IOException e) {
         	System.out.println("Problem with the creation 3D file");
         	System.exit(0);
         }
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
		cpomdp pomdp = new cpomdp(filename);
		pomdp.DISPLAY_2D = Boolean.parseBoolean(args[2]);
		pomdp.DISPLAY_3D = Boolean.parseBoolean(args[3]);
		System.out.println(pomdp.toString(false, false));
		//System.in.read();

		int iter_used = pomdp.solve(iter);
		System.out.println("\nSolution complete, required " + 
				iter_used + " / " + iter + " iterations.");
	}

}
