//////////////////////////////////////////////////////////////////////
//
// Extended Algebraic Decision Diagrams
//
// Decision tests have labels -- either boolean variables or arithmetic
//                               expressions (could be relational expressions
//                               as well -- same as FOADD, but not used here)
//                               Need a list of decisions (type: var, expr)
// 
//                               leaves are expressions (can be constants)
//
//////////////////////////////////////////////////////////////////////

package xadd;

import graph.Graph;

import java.io.PrintStream;
import java.io.Serializable;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import logic.kb.fol.FOPC;
import logic.kb.prop.PropKbCNF;
import lpsolve.LP;
import lpsolve.LpSolve;
import util.IntPair;
import util.IntTriple;
import util.MapList;
import util.Pair;
import xadd.XADD.Expr;
import cmdp.HierarchicalParser;

/**
 * General class for implementation of ADD data structure
 **/
public class XADD {

	// Visualization
	public final static boolean GRAPH_USE_COLOR = true;
	// Flags
	public final static boolean USE_CANONICAL_NODES = true; // Store nodes in canonical format?
	public final static boolean CHECK_MIN_MAX = false; // Will be buggy if min/max of expr
	public final static boolean USE_MINUS_COMP = false; // Error, all max/min comps reduce to false!
	public final static int MAX_BRANCH_COUNT = 1000000;
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < amt
	public static Runtime RUNTIME = Runtime.getRuntime();

	// Debug
	public final static boolean CHECK_LOCAL_ORDERING = true;
	public final static boolean SHOW_DECISION_EVAL = false;
	public final static boolean DEBUG_EVAL_RANGE = false;
	public final static boolean DEBUG_CONSTRAINTS = false;
	public final static boolean HANDLE_NONLINEAR = false;
	public final static boolean CHECK_PATH_REDUNDANCY=true;
	public final static boolean MAINTAIN_PAIRWISE_IMPLICATIONS = true;
	//Functions
	public static boolean REDUCE_LP = true;
	// Operators
	public final static int UND = 0;
	public final static int SUM = 1;
	public final static int MINUS = 2;
	public final static int PROD = 3;
	public final static int DIV = 4;
	public final static int MAX = 5;
	public final static int MIN = 6;
	public final static int RESTRICT_LOW = 7;
	public final static int RESTRICT_HIGH = 8;
	public final static int EQ = 9;
	public final static int NEQ = 10;
	public final static int GT = 11;
	public final static int GT_EQ = 12;
	public final static int LT = 13;
	public final static int LT_EQ = 14;
	public final static int LINEARIZE = 15;
	public final static int ERROR = 16;
	public final static int ROUND = 17;
	public final static String[] _aOpNames = {/* 0 */"UND",
		/* 1 */"+", "-", "*", "/", "max", "min", "|l", "|h",
		/* 9 */"=", "!=", ">", ">=", "<", "<=", "ERROR" };
	// constants for division
	public static ArrayList<ArithExpr> showDiv = new ArrayList<XADD.ArithExpr>();
	public static HashMap<Integer, Boolean> lastDecision = new HashMap<Integer, Boolean>();

	public int changed_var_index = -1;
	// Constants
	public final static String STRING_TAB = "   ";
	public final static DecimalFormat _df = new DecimalFormat("#.########################");
	public final static DecimalFormat _df_unformatted = new DecimalFormat("#.########################");
	public final static ArithExpr ZERO = new DoubleExpr(0d);
	public final static ArithExpr ONE = new DoubleExpr(1d);
	public final static ArithExpr NEG_ONE = new DoubleExpr(-1d);
	public final static ArithExpr NEG_INFINITE = new DoubleExpr(-1000000d);
	public final static ArithExpr POS_INFINITE = new DoubleExpr(1000000d);

	// Variable Maintenance
	public ArrayList<Decision> _alOrder = new ArrayList<Decision>();
	// Node Maintenance
	public int _markCounter = 1;
	public int _nodeCounter = 1;
	public HashMap<XADDNode, Integer> _hmNode2Int = new HashMap<XADDNode, Integer>();
	public HashMap<Integer, XADDNode> _hmInt2Node = new HashMap<Integer, XADDNode>();
	// Reduce & Apply Caches
	public HashMap<IntTriple, Integer> _hmReduceCache = new HashMap<IntTriple, Integer>();
	public HashMap<IntTriple, Integer> _hmReduceLPCache = new HashMap<IntTriple, Integer>();
	public HashMap<IntPair, Integer> _hmReduceLeafOpCache = new HashMap<IntPair, Integer>();
	public HashMap<IntPair, Integer> _hmReduceAnnotateCache = new HashMap<IntPair, Integer>();
	public HashMap<IntTriple, Integer> _hmApplyCache = new HashMap<IntTriple, Integer>();
	public HashMap<XADDINode, HashSet<String>> _hmINode2Vars = new HashMap<XADDINode, HashSet<String>>();
	public HashMap<Integer, Pair<XADDNode, XADDNode>> _hmLinearDecisions = new HashMap<Integer, Pair<XADDNode, XADDNode>>();

	public ArrayList<String> _hsBooleanVars = new ArrayList<String>();
	public ArrayList<String> _alBooleanVars = new ArrayList<String>();
	public HashMap<String, Integer> _cvar2ID;
	//public static ArrayList<String> _hmContinuousVars;
	private static /*static*/ ArrayList<String> _alContinuousVars;
	private HashSet<String>   _hsContinuousVars;

	public HashMap<String, Double> _hmMinVal = new HashMap<String, Double>();
	public HashMap<String, Double> _hmMaxVal = new HashMap<String, Double>();

	// Implication Cache
	public MapList _mlImplications = new MapList();
	public MapList _mlNonImplications = new MapList();
	public MapList _mlImplicationsChild = new MapList();
	public MapList _mlIntermediate = new MapList();
	public HashMap<Integer,ArrayList<Integer>> _hmIntermediate = new HashMap<Integer, ArrayList<Integer>>();

	// Flush
	public HashSet<Integer> _hsSpecialNodes = new HashSet<Integer>();
	public HashMap<XADDNode, Integer> _hmNode2IntNew = new HashMap<XADDNode, Integer>();
	public HashMap<Integer, XADDNode> _hmInt2NodeNew = new HashMap<Integer, XADDNode>();

	// Methods
	public XADD() {
		// Ensure that the 0th decision ID is invalid
		_alOrder.add(new NullDec());
		_alContinuousVars = new ArrayList<String>();
		_hsContinuousVars = new HashSet<String>();
		//_hmContinuousVars = new ArrayList<String>();
		_cvar2ID = new HashMap<String, Integer>();
	}

	public ArrayList<String> getContinuousVarList() {
		return (ArrayList<String>)_alContinuousVars.clone();
	}


	/*public ArrayList<String> get_hmContinuousVars() {
		return _hmContinuousVars;
	}

	public void set_hmContinuousVars(ArrayList<String> _hmContinuousVars) {
		this._hmContinuousVars = _hmContinuousVars;
	}*/

	public int getBoolVarIndex(String bool_name) {
		return getVarIndex(new BoolDec(bool_name), false);
	}

	public int getVarIndex(Decision d) {
		return getVarIndex(d, false);
	}
	// Note: var index can never be 0, negative var index now means negated decision
	public int getVarIndex(Decision d, boolean create) {

		if (USE_CANONICAL_NODES) {
			// System.out.println(">> Before canonical: " + d);
			/*if (d instanceof ExprDec)
			{
				ExprDec e = (ExprDec) d;
				if ((e._expr._lhs instanceof DoubleExpr) && (e._expr._rhs instanceof DoubleExpr));
				else d = d.divideRound(e);
			}
				d = d.divideRound((ExprDec)d);*/
			d = d.makeCanonical();
			// System.out.println(">> After canonical: " + d);
		}
		int index = _alOrder.indexOf(d);
		// If not found, try negating d
		if (index < 0 && d instanceof ExprDec) 
		{
			CompExpr comp = ((ExprDec) d)._expr;
			// ArithExpr lhs = comp._lhs;
			// ArithExpr rhs = comp._rhs;
			// lhs = new OperExpr(PROD, NEG_ONE, lhs);
			// rhs = new OperExpr(PROD, NEG_ONE, rhs);
			// CompExpr neg_comp = new CompExpr(
			// CompExpr.flipCompOper(comp._type), lhs, rhs );
			CompExpr neg_comp = new CompExpr(CompExpr.flipCompOper(comp._type),	comp._lhs, comp._rhs);
			Decision neg_d = new ExprDec(neg_comp).makeCanonical();

			index = _alOrder.indexOf(neg_d);
			if (index > 0)
				index = -index;
			else
				index = 0; // No valid decision has index 0
		} else if (index < 0) {
			index = 0; // No valid decision has index 0
		}

		if (index != 0 || !create) // Valid index found
			return index;
		else {
			_alOrder.add(d);
			index= _alOrder.size() - 1;
		
		if (d instanceof ExprDec) {
			HashSet<String> all_vars = new HashSet<String>();
			((ExprDec)d)._expr.collectVars(all_vars);
			for (String s : all_vars)
				// Boolean variables would have been added immediately in BoolDec
				// so are already in _hsBooleanVars
				if (!_hsBooleanVars.contains(s) && !_hsContinuousVars.contains(s)) {
					_hsContinuousVars.add(s);
					_alContinuousVars.add(s);
				}
			}
		return index;
		}
	}

	public int getTermNode(XADDTNode n) {
		return getTermNode(n._expr, n._annotate); 
	}

	public int getTermNode(ArithExpr e) {
		return getTermNode(e, null);
	}

	// This version can handle annotations
	public XADDTNode _tempTNode = new XADDTNode(null,null);

	public int getTermNode(ArithExpr e, Object annotation) {

		if (USE_CANONICAL_NODES)
			e = (ArithExpr) e.makeCanonical();

		_tempTNode.set(e, annotation);
		Integer id = _hmNode2Int.get(_tempTNode);
		if (id == null) {
			// Not in cache so create
			id = _nodeCounter;
			XADDTNode node = new XADDTNode(e, annotation);
			_hmNode2Int.put(node, id);
			_hmInt2Node.put(id, node);
			_nodeCounter++;

			// Add in all new continuous variables
			HashSet<String> all_vars = new HashSet<String>();
			node._expr.collectVars(all_vars);
			for (String s : all_vars)
				// Boolean variables would have been added immediately in BoolDec
				// so are already in _hsBooleanVars
				if (!_hsBooleanVars.contains(s) && !_hsContinuousVars.contains(s)) {
					_hsContinuousVars.add(s);
					_alContinuousVars.add(s);
				}
		}
		return id;
	}

	public int getVarNode(Decision d, double low_val, double high_val) {
		int var = getVarIndex(d, true);
		int low = getTermNode(new DoubleExpr(low_val));
		int high = getTermNode(new DoubleExpr(high_val));
		return getINode(var, low, high);
	}

	public XADDNode getNode(int node_id) {
		return _hmInt2Node.get(node_id);
	}

	public XADDINode _tempINode = new XADDINode(-1, -1, -1);
	public int getINode(int var, int low, int high) {

		if (var < 0) {
			int temp = low;
			low = high;
			high = temp;
			var = -var;
		}
		if (low < 0 || high < 0) {
			System.err.println("Invalid node (low,high)=(" + low + "," + high
					+ ") for var: " + var);
			new Exception().printStackTrace();
			System.exit(1);
		}

		// First check if low == high... in this case, just perform the
		// obvious equivalent reduction (this saves headaches later)
		if (low == high) {
			return low;
		}

		// Handle tautological variables
		Decision d = _alOrder.get(var);
		if (d instanceof TautDec) {
			if (((TautDec) d)._bTautology)
				return high;
			else
				return low;
		}
		// Retrieve inode (and create if it does not exist)
		_tempINode.set(var, low, high);
		Integer id = _hmNode2Int.get(_tempINode);
		if (id == null) {
			// Not in cache so create
			id = _nodeCounter;
			XADDINode node = new XADDINode(var, low, high);
			_hmNode2Int.put(node, id);
			_hmInt2Node.put(id, node);
			_nodeCounter++;
		}
		return id;
	}

	// Returns all variables in this XADD
	public HashSet<String> collectVars(int id) {
		XADDNode n = _hmInt2Node.get(id);
		if (n == null) {
			System.out.println("ERROR: " + id + " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}
		return n.collectVars();
	}
	// //////////////////////////////////////////////////////////////

	public int buildCanonicalXADD(ArrayList l) {
		if (l.size() == 1) {
			// Terminal node// System.out.println("Parsing: '" + l.get(0) + "'");
			if (!(l.get(0) instanceof String)) {
				System.err.println("Cannot parse terminal: '" + l.get(0)
						+ "'\n... make sure terminals are surrounded in [ ]");
				System.exit(1);
			}
			String s = (String) l.get(0);
			// Work around a parser issue with singleton vars in brackets
			if (s.startsWith("["))
				s = s.substring(1, s.length() - 1);
			int n = ArithExpr.parseIntoXADD(this, s);
			if (n < 0) {
				System.err.println("Failed to parse: '" + s + "'");
				System.exit(1);
			}
			return n;
		} else if (l.size() == 3) {
			// Internal node
			String expr = ((String) l.get(0));
			Decision d = null;
			// System.out.println("Expr: " + expr);
			if (expr.startsWith("[")) {
				CompExpr c = CompExpr.parse(expr);
				if (c != null) {
					// System.out.println("CompExpr: " + c);
					d = new ExprDec(c);
				}
			} else {
				d = new BoolDec(expr);
			}

			if (d == null) {
				System.out.println("Could not buildNonCanonicalXADD for terminal '"	+ l + "'");
				return -1;
			} else {
				// System.out.println("Var expr: " + d);
				int var = getVarIndex(d, true);
				int high = buildCanonicalXADD((ArrayList) l.get(1));
				int low = buildCanonicalXADD((ArrayList) l.get(2));

				int T_ZERO = getTermNode(ZERO);
				int T_ONE = getTermNode(ONE);
				int ind_true = getINode(var, /* low */T_ZERO, /* high */T_ONE);
				int ind_false = getINode(var, /* low */T_ONE, /* high */T_ZERO);
				int true_half = applyInt(ind_true, high, PROD); // Note:this enforces canonicity so
				int false_half = applyInt(ind_false, low, PROD); // can use applyInt rather than apply

				// System.out.println("New inode: " + index + " - " + low + ", " + high);
				// System.out.println("Var: " + _alOrder.get(index));
				return applyInt(true_half, false_half, SUM);
			}
		} else {
			// Unknown
			System.out.println("Could not buildNonCanonicalXADD for "+ l.size() + " args '" + l + "'");
			return -1;
		}
	}

	public int buildNonCanonicalXADD(ArrayList l) {
		if (l.size() == 1) {
			// Terminal node
			String s = (String) l.get(0);
			// Work around a parser issue with singleton vars in brackets
			if (s.startsWith("["))
				s = s.substring(1, s.length() - 1);
			ArithExpr a = ArithExpr.parse(s);
			if (a == null) {
				// System.out.println("Could not buildNonCanonicalXADD for terminal '"
				// + (String)l.get(0) + "'");
				return -1;
			} else
				return getTermNode(a);
		} else if (l.size() == 3) {
			// Internal node
			String expr = ((String) l.get(0));
			Decision d = null;
			// System.out.println("Expr: " + expr);
			if (expr.startsWith("[")) {
				CompExpr c = CompExpr.parse(expr);
				if (c != null) {
					// System.out.println("CompExpr: " + c);
					d = new ExprDec(c);
				}
			} else {
				d = new BoolDec(expr);
			}

			if (d == null) {
				System.out.println("Could not buildNonCanonicalXADD for terminal '"	+ l + "'");
				return -1;
			} else {
				// System.out.println("Var expr: " + d);
				int index = getVarIndex(d, true);
				int high = buildNonCanonicalXADD((ArrayList) l.get(1));
				int low = buildNonCanonicalXADD((ArrayList) l.get(2));
				// System.out.println("New inode: " + index + " - " + low + ", " + high);
				// System.out.println("Var: " + _alOrder.get(index));
				return getINode(index, low, high);
			}
		} else {
			// Unknown
			System.out.println("Could not buildNonCanonicalXADD for "+ l.size() + " args '" + l + "'");
			return -1;
		}
	}

	public int getBranchCount(int id) {
		XADDNode root = _hmInt2Node.get(id);
		return root.countBranches();
	}

	public int getNodeCount(int id) {
		XADDNode root = _hmInt2Node.get(id);
		return root.collectNodes().size();
	}

	// ////////////////////////////////////////////////////////////////////

	public Graph getGraph(int id) {
		Graph g = new Graph(true /* directed */, false /* bottom-to-top */,
				false /* left-to-right */, true /* multi-links */);
		XADDNode root = _hmInt2Node.get(id);
		root.toGraph(g, id);
		return g;
	}

	public String getString(int id) {
		return getString(id, true);
	}

	public String getString(int id, boolean format) {
		XADDNode root = _hmInt2Node.get(id);
		int num_nodes = getNodeCount(id);
		if (num_nodes > 40)
			return "[XADD " + id + " contains " + num_nodes + " nodes... too large to print]";
		else
			return root.toString(format);
	}
	// ////////////////////////////////////////////////////////////////////

	// TODO: Implement garbage collection with my counter increment trick
	// and marking.

	public IntTriple _tempReduceKey = new IntTriple(-1, -1, -1);
	public int reduce(int node) 
	{
		return reduceOp(node, -1, -1);
	}

	public int opOut(int node_id, int var_id, int op) {
		int ret = reduceOp(node_id, var_id, op);

		// operations like sum and product may get decisions out of order
		// (reduce low / high should not do this)
		// TODO: is this right?
		if (op == SUM || op == PROD)
			return makeCanonical(ret);
		else
			return ret;
	}

	private int reduceOp(int node_id, int var_id, int op) {

		if (var_id < 0 && op >= 0) {
			System.err.println("Illegal op-code '" + op + "' for var id: "
					+ var_id);
			new Exception().printStackTrace();
			System.exit(1);
		}

		Integer ret = null;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n == null) {
			System.out.println("ERROR: " + node_id	+ " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		// by default if hashing and equality testing are working in getTNode
		if (n instanceof XADDTNode) {
			return node_id; // Assuming that to have a node id means canonical
		}

		// If its an internal node, check the reduce cache
		_tempReduceKey.set(node_id, var_id, op);
		if ((ret = _hmReduceCache.get(_tempReduceKey)) != null) {
			// System.out.println("In cache, returning: " + qret);
			return ret;
		}

		XADDINode inode = (XADDINode) n;

		int low = -1;
		int high = -1;
		if (op != RESTRICT_HIGH || var_id != inode._var) {
			low = reduceOp(inode._low, var_id, op);
		}
		if (op != RESTRICT_LOW || var_id != inode._var) {
			high = reduceOp(inode._high, var_id, op);
		}

		if (op != -1 && var_id != -1 && var_id == inode._var) {
			// ReduceOp
			if (op == RESTRICT_LOW) {
				ret = low;
			} else if (op == RESTRICT_HIGH) {
				ret = high;
			} else if (op == SUM || op == PROD) { // op \in {MINUS, DIV} not
				// commutative
				// not obvious if low or high comes first
				ret = apply(low, high, op); // may not be canonical, but will be
				// fixed
			} else {
				System.out
				.println("ERROR: id:"+ op+ "/ name:"+ _aOpNames[op]	+ " expected in node cache, but not found!  (Or illegal op.)");
				new Exception().printStackTrace();
				System.exit(1);
			}
		} else {
			// Standard Reduce: getInode will handle the case of low == high
			ret = getINode(inode._var, low, high);
		}

		// Put return value in cache and return
		_hmReduceCache.put(new IntTriple(node_id, var_id, op), ret);
		return ret;
	}
	// NOTE: can only linearize decisions that have one quadratic variable,
	//       otherwise have to complete the square symbolically and take
	//       a symbolic square root of an XADD... OK except that no longer
	//       a polynomial for purposes of current code.
	public int reduceLinearize(int node_id) {
		node_id = reduceLinearizeInt(node_id);
		return makeCanonical(node_id); // Nodes may have gotten out of order
	}

	public int reduceLinearizeInt(int node_id) {

		Integer ret = null;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n == null) {
			System.out.println("ERROR: " + node_id
					+ " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		// by default if hashing and equality testing are working in getTNode
		if (n instanceof XADDTNode) {
			return node_id; // Assuming that to have a node id means canonical
		}

		// If its an internal node, check the reduce cache
		_tempReduceKey.set(node_id, -1, LINEARIZE);
		if ((ret = _hmReduceCache.get(_tempReduceKey)) != null) {
			// System.out.println("In cache, returning: " + qret);
			return ret;
		}

		XADDINode inode = (XADDINode) n;

		int low = reduceLinearizeInt(inode._low);
		int high = reduceLinearizeInt(inode._high);

		Decision d = _alOrder.get(inode._var);

		// For now we'll only do linearization of quadratic decisions
		Integer xadd_dec_true = linearizeQuadDecision(d);
		if (xadd_dec_true == null)
			ret = getINode(inode._var, low, high);
		else {
			int xadd_dec_false = applyInt(getTermNode(ONE), xadd_dec_true,
					MINUS); // can use applyInt rather than apply
			int true_half = applyInt(xadd_dec_true, high, PROD); // Note: this
			// enforces
			// canonicity
			// so
			int false_half = applyInt(xadd_dec_false, low, PROD); // can use
			// applyInt
			// rather
			// than
			// apply
			ret = applyInt(true_half, false_half, SUM);
		}

		// Put return value in cache and return
		_hmReduceCache.put(new IntTriple(node_id, -1, LINEARIZE), ret);
		return ret;
	}

	// Returns XADD for true branch indicator of decision, otherwise null
	public Integer linearizeQuadDecision(Decision d) {

		if (!(d instanceof ExprDec))
			return null;

		ExprDec e = (ExprDec) d;
		OperExpr lhs = (OperExpr) e._expr._lhs;
		if (lhs._type != SUM)
			return null;

		HashSet<String> cont_vars = new HashSet<String>();
		d.collectVars(cont_vars);

		for (String var : cont_vars) {

			// Bookkeeping variables
			VarExpr varExpr = new VarExpr(var);
			boolean all_var = true;
			boolean higher_order = false;
			Double quad_coef = null;
			double linear_coef = 0d;
			double const_coef = 0d;

			// Set coefficients
			for (ArithExpr a : lhs._terms) {

				if (a instanceof OperExpr && ((OperExpr) a)._type == PROD) {

					// Count order of polynomial in var
					int count_var = 0;
					Double coef = null;
					for (ArithExpr a_sub : ((OperExpr) a)._terms) {
						if (a_sub.equals(varExpr))
							count_var++;
						else if (a_sub instanceof DoubleExpr)
							coef = ((coef == null) ? ((DoubleExpr) a_sub)._dConstVal
									: coef * ((DoubleExpr) a_sub)._dConstVal);
						else {
							all_var = false;
							break;
						}
					}

					// Set appropriate coefficients
					if (count_var > 2) {
						higher_order = true;
						break;
					} else if (count_var == 2)
						quad_coef = quad_coef == null ? coef : quad_coef + coef;
					else if (count_var == 1)
						linear_coef += coef;
					else if (count_var == 0)
						const_coef += coef;

				} else if (a instanceof VarExpr) {
					linear_coef += 1d;
				} else if (a instanceof DoubleExpr) {
					const_coef += ((DoubleExpr) a)._dConstVal;
				}
			}

			// If this is a quadratic expression in one variable, we can
			// linerize and return the true indicator XADD for it
			if (all_var && !higher_order && quad_coef != null) {

				// Build XADD for new decision true indicator and return
				// ax^2 + bx + c COMP 0
				// => x^2 + b/a*x COMP -c/a
				// let d = b/a and e = -c/a
				// if (a < 0) COMP = flip(COMP)
				// => x^2 + d*x + (d/2)^2 COMP (d/2)^2 + e
				// => (x + d/2)^2 COMP (d/2)^2 + e
				// => (x + d/2) COMP SQRT((d/2)^2 + e)
				// ^ (x + d/2) flip(COMP) -SQRT((d/2)^2 + e)
				double var_d = linear_coef / quad_coef;
				double var_e = -const_coef / quad_coef;

				// Build expressions for first and second inequality
				int comp_oper = e._expr._type;
				if (quad_coef < 0)
					comp_oper = CompExpr.flipCompOper(comp_oper);
				int flip_comp_oper = CompExpr.flipCompOper(comp_oper);
				OperExpr lhs_expr = new OperExpr(SUM, new VarExpr(var),
						new DoubleExpr(var_d / 2d));
				double rhs_const = Math.sqrt(var_e + var_d * var_d / 4d);
				int var1_id = getVarIndex(new ExprDec(new CompExpr(comp_oper,
						lhs_expr, new DoubleExpr(rhs_const))), true);
				int var2_id = getVarIndex(new ExprDec(new CompExpr(
						flip_comp_oper, lhs_expr, new DoubleExpr(-rhs_const))),
						true);

				// Build XADD indicator from expressions
				// Note: disjunction 'a v b = 1 - (1 - a)*(1 - b)
				int T_ZERO = getTermNode(ZERO);
				int T_ONE = getTermNode(ONE);
				int expr1_xadd = getINode(var1_id, /* low */T_ONE, /* high */
						T_ZERO);
				int expr2_xadd = getINode(var2_id, /* low */T_ONE, /* high */
						T_ZERO);
				int ret_xadd = apply(T_ONE,
						apply(expr1_xadd, expr2_xadd, PROD), MINUS);
				/*System.out.println("LINEARIZE -- started with: " + e
						+ "... returning\n" + getString(ret_xadd));*/
				// System.exit(1);
				return ret_xadd;
			}
		} // Done processing 'var'

		return null; // We didn't find a quadratic before this
	}

	IntPair _tempReduceAnnotateKey = new IntPair(-1, -1);
	public int annotateXADD(int node_id, Object annotation)
	{
		Integer ret = null;
		XADDNode node = _hmInt2Node.get(node_id);
		if (node == null) {
			System.out.println("ERROR: " + node_id + " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// Directly annotate terminal nodes only 
		if ((node instanceof XADDTNode)) {

			XADDTNode tnode = (XADDTNode)node;
			return getTermNode(tnode._expr, annotation);
		}

		// If its an internal node, first check the annotate cache
		_tempReduceAnnotateKey.set(node_id, annotation.hashCode());
		if 	((ret = _hmReduceAnnotateCache.get(_tempReduceAnnotateKey)) != null)
			return ret;

		// Not annotated before so recursively annotate
		XADDINode inode = (XADDINode) node;
		int low  = annotateXADD(inode._low, annotation);
		int high = annotateXADD(inode._high, annotation);
		ret = getINode(inode._var, low, high);
		_hmReduceAnnotateCache.put(new IntPair(node_id, annotation.hashCode()), ret);
		return ret;
	}
	//rounding the final result xadd to reduce the number of nodes
	/*public int reduceRound(int node_id)
	{
		ArrayList<Integer> redundantDec = new ArrayList<Integer>();
		int ret = reduceRound(node_id,redundantDec);
		for (int i=0;i<redundantDec.size();i++)
			_alOrder.remove(i);
		return ret;
	}*/
	public int reduceRound(int node_id) {

		Integer ret = null;
		int low = 0,high=0;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n == null) {
			System.out.println("ERROR: " + node_id
					+ " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		if (n instanceof XADDTNode) 
		{
			//consider dividing all coeff by first coeff and then round ( can help with pruning)
			ArithExpr tempExpr = ((XADDTNode)n)._expr;
			if (tempExpr instanceof DoubleExpr)
				((DoubleExpr)tempExpr)._dConstVal = Math.round(((DoubleExpr)tempExpr)._dConstVal*1000d)/1000d ; 
			else if (tempExpr instanceof OperExpr)
			{
				OperExpr oper_expr = (OperExpr) tempExpr;
				// sum of products, for each sum term:
				for (ArithExpr e : oper_expr._terms) 
				{
					if (e instanceof DoubleExpr)
						((DoubleExpr)e)._dConstVal = Math.round(((DoubleExpr)e)._dConstVal*1000d)/1000d ; 
					else if (e instanceof OperExpr)
					{
						// inside each product term
						if (((OperExpr) e)._type == PROD) // for each of the products:
							for (ArithExpr e1 : ((OperExpr) e)._terms) 
								if (e1 instanceof DoubleExpr)
									((DoubleExpr)e1)._dConstVal = Math.round(((DoubleExpr)e1)._dConstVal*1000d)/1000d ; 
					}
				}
			}
			return node_id; // Assuming that to have a node id means canonical
		}

		// If its an internal node, check the reduce cache
		_tempReduceKey.set(node_id, -1, ROUND);
		if ((ret = _hmReduceCache.get(_tempReduceKey)) != null) 
			return ret;


		XADDINode inode = (XADDINode) n;

		Decision d = _alOrder.get(inode._var);
		ExprDec e = null,e1=null;
		/////////// For internal node also makeCanonical by dividing coeff of first variable by rest of the variables
		//check if this division followed by rounding causes the node to be redundant, then use the varIndex of this node instead
		if (d instanceof ExprDec)
		{
			//ExprDec e = (ExprDec) d;
			////////////////////////added
			e1 = (ExprDec)d;
			e = e1.clone();
			// For decision node also makeCanonical by dividing coeff of first variable by rest of the variables
			ArithExpr new_lhs = ArithExpr.op(e._expr._lhs, e._expr._rhs,MINUS);
			new_lhs = (ArithExpr) new_lhs.makeCanonical();
			CompExpr current_expr = new CompExpr(e._expr._type, new_lhs, ZERO);
			String contVar = null;
			for (int i = 0; i < _alContinuousVars.size(); i++) {
				contVar = _alContinuousVars.get(i);
				DoubleExpr doubleCoef = (DoubleExpr) ZERO;
				// first look for x*x
				if (HANDLE_NONLINEAR)
					doubleCoef = findVar(current_expr._lhs, contVar,true);
				if (doubleCoef == (DoubleExpr) ZERO)
					doubleCoef = findVar(current_expr._lhs, contVar,false);
				if (doubleCoef != (DoubleExpr) ZERO) 
				{
					boolean flip_comparison = false;
					flip_comparison = (doubleCoef._dConstVal < 0d)&& (current_expr._type != EQ)&& (current_expr._type != NEQ);

					current_expr._lhs = (ArithExpr) (new OperExpr(PROD,	(ArithExpr.op(new DoubleExpr(1d),doubleCoef, DIV)),
									current_expr._lhs)).makeCanonical();
					int comp_oper = current_expr._type;
					if (flip_comparison)
						switch (comp_oper) 
						{
						case GT:
							current_expr._type = LT;
							break;
						case GT_EQ:
							current_expr._type = LT_EQ;
							break;
						case LT:
							current_expr._type = GT;
							break;
						case LT_EQ:
							current_expr._type = GT_EQ;
							break;
						}

					// ((ExprDec) d)._expr = comp;
					break;
				}
			}
			e._expr = current_expr;
				
			
			///////////////////////
			OperExpr lhs = (OperExpr) e._expr._lhs;
			for (ArithExpr a : lhs._terms)
			{

				if (a instanceof OperExpr && ((OperExpr) a)._type == PROD) 
				{

					for (ArithExpr a1 : ((OperExpr) a)._terms) 
						if (a1 instanceof DoubleExpr)
							((DoubleExpr)a1)._dConstVal = Math.round(((DoubleExpr)a1)._dConstVal*1000d)/1000d ; 

				} 
				else if (a instanceof DoubleExpr) 
					((DoubleExpr)a)._dConstVal = Math.round(((DoubleExpr)a)._dConstVal*1000d)/1000d ; 

			}
			//////////////////////added
			Decision d1 = new ExprDec(e._expr);
			int currentIndex = getVarIndex(d1,true);
			/*CompExpr neg_comp = new CompExpr(CompExpr.flipCompOper(e._expr._type),e._expr._lhs, e._expr._rhs);
			Decision neg_d = new ExprDec(neg_comp);
			int index = getVarIndex(neg_d,false);*/
			if (currentIndex>0/*(index< currentIndex) && (index>0)*/) 
			{
				inode._var = currentIndex;
				e1 = e;
				low = reduceRound(inode._low);
				high = reduceRound(inode._high);
			}
			//inode._var = getVarIndex(e,true);
			else if (currentIndex < 0)
			{
				//don't change the currentIndex if it is smaller than the negative decision 
				// it was added earlier than index or it is a new index
				inode._var = Math.abs(currentIndex);
				e1 = e;
				high = reduceRound(inode._low);
				low = reduceRound(inode._high);
			}
		}
		else 
		{
			//not exprDec
			low = reduceRound(inode._low);
			high = reduceRound(inode._high);
		}

			
			////////////////////////
	
		/*}
		int low = reduceRound(inode._low);
		int high = reduceRound(inode._high);*/

		ret = getINode(inode._var, low, high);
		// Put return value in cache and return
		_hmReduceCache.put(new IntTriple(node_id, -1, ROUND), ret);
		return ret;
	}


	public IntTriple _tempReduceLPKey = new IntTriple(-1, -1, -1);

	public int reduceLP(int node_id) {
		ArrayList<Integer> test_var = new ArrayList<Integer>();
		ArrayList<Boolean> test_dec = new ArrayList<Boolean>();
		for (int i = 0; i < _alOrder.size(); i++) {
			test_dec.add(null);
		}
		return reduceLP(node_id, test_var, test_dec);

	}

	public int reduceLP(int node_id, boolean performRedundancy) {
		ArrayList<Integer> test_var = new ArrayList<Integer>();
		ArrayList<Boolean> test_dec = new ArrayList<Boolean>();
		_mlImplicationsChild = new MapList();
		//_mlIntermediate = new MapList();
		_mlImplications = new MapList();
		_mlNonImplications = new MapList();
		//HashMap<Integer,Boolean> marked_nodes = new HashMap<Integer,Boolean>();
		//definitions for paths to a node
		ArrayList<Integer> path = new ArrayList<Integer>();
		ArrayList<ArrayList<Integer>> path_no = new ArrayList<ArrayList<Integer>>();
		HashMap <Integer,ArrayList<ArrayList<Integer>>> formulas = new HashMap<Integer, ArrayList<ArrayList<Integer>>>();
		//List for keeping track of false-true branch id's
		int[][] branch_id = new int[1000][2];
		for (int i = 0; i < _alOrder.size(); i++) {
			test_dec.add(null);
		}
		int tree = reduceLP(node_id, test_var, test_dec);
		for (int i = 0; i < _alOrder.size(); i++) {
			test_dec.add(null);
		}
		/*Graph g2 = getGraph(tree);
		g2.addNode("_temp_");
		g2.addNodeLabel("_temp_", "V^ After consistency check and before Redundancy check");
		g2.addNodeShape("_temp_", "square");
		g2.addNodeStyle("_temp_", "filled");
		g2.addNodeColor("_temp_", "gold1");
		g2.genDotFile("V^ before Redundancy check.dot");
		g2.launchViewer(1300, 770);*/
		//put formula for root node
		path.add(0);
		path_no.add(path);
		formulas.put(tree, path_no);
		//add all implications to KB
		PropKbCNF kb = new PropKbCNF();
		kb.addFormula("((p^~p) <=> (false))");
		kb.addFormula("((p|~p) <=> (true))");
		_hmIntermediate = new HashMap<Integer, ArrayList<Integer>>();
		ArrayList<Integer> _dl = new ArrayList<Integer>();
		//there are many implications not in this reduced tree, so take them out and also define the new paths of the tree
		getDecisionList(tree,_dl,test_var);
		Iterator it = _mlImplicationsChild.keySet().iterator();
		//
		//Add implications to KB
		//
		while (it.hasNext())
		{
			int parent = (Integer) it.next();
			//check if decision is inside the reduced tree 
			if (_dl.contains(Math.abs(parent)))
			{
				ArrayList<Integer> child = _mlImplicationsChild.getValues(parent);
				for (int j=0;j<child.size();j++)
				{
					//check if decision is inside the reduced tree + there is a path from parent to child
					if (_dl.contains(Math.abs(child.get(j))))
					{
						for (int i=0;i<_hmIntermediate.size();i++)
							if ((_hmIntermediate.get(i).contains(parent)) && (_hmIntermediate.get(i).contains(child.get(j))))
							{
								String p="",c="";
								if (parent <0) 
									p = " ~a"+Math.abs(parent)+"a ";
								else p = " a"+Math.abs(parent)+"a ";
								if (child.get(j) <0) 
									c = "~a"+Math.abs(child.get(j))+"a";
								else 
									c = " a"+Math.abs(child.get(j))+"a ";
								String s = p+ " =>" +c; 
								kb.addFormula(s);
								break;
							}
					}
				}
			}
		}
		if (performRedundancy)
			return reduceRedundancy(tree,formulas,kb);
		else return tree;
	}


	private int getDecisionList(int node_id,ArrayList<Integer> _decisionList,ArrayList<Integer> test_var) {
		Integer ret = null;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n instanceof XADDTNode) {
			//add this path to the set of intermediate paths
			ArrayList<Integer> temp = new ArrayList<Integer>();
			for (int par_dec : test_var)
			{
				//par_dec = test_var.get(par_dec) ? par_dec : -par_dec;
				temp.add(par_dec);
			}
			//temp.add(inode._var);
			int sizeInt = _hmIntermediate.size();
			_hmIntermediate.put(sizeInt,temp);
			return node_id; 
		}
		else {
			XADDINode inode = (XADDINode) n;
			_decisionList.add(inode._var);

			test_var.add(-inode._var);
			int low = getDecisionList(inode._low, _decisionList,test_var);
			test_var.set(test_var.size() - 1, inode._var);
			int high = getDecisionList(inode._high, _decisionList, test_var);
			test_var.remove(test_var.size() - 1);

			ret = getINode(inode._var, low, high);
		}
		return ret;
	}

	private int reduceLP(int node_id, ArrayList<Integer> test_var, ArrayList<Boolean> test_dec) 
	{

		Integer ret = null;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n == null) {
			System.out.println("ERROR: " + node_id + " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		// by default if hashing and equality testing are working in getTNode
		if (n instanceof XADDTNode) {
			return node_id; // Assuming that to have a node id means canonical
		}
		_tempReduceLPKey.set(node_id, test_var.hashCode(), test_dec.hashCode());
		if (/*false && */(ret = _hmReduceLPCache.get(_tempReduceLPKey)) != null) 
		{
			//System.out.println("In cache, returning: " + ret);
			return ret;
		}
		XADDINode inode = (XADDINode) n;

		// Reduce based on pairwise interactions only
		Boolean var_implication = null;

		// top-bottom do total implication, just store the implications (do nothing in singleImplied)
		// bottom-up do pairwise comparison
		//if (MAINTAIN_PAIRWISE_IMPLICATIONS) {

		// Pairwise implication test only

		for (int par_dec : test_var) {
			par_dec = test_dec.get(par_dec) ? par_dec : -par_dec; // Negate if false
			if (isSingleDecImplied(par_dec, inode._var)); 
			//var_implication = true;
			else if (isSingleDecImplied(par_dec, -inode._var));
			//var_implication = false;
			//if (var_implication != null) 	break;
		} 
		//} else {

		// Full branch implication test
		if (isTestImplied(test_var, test_dec, inode._var, true)) {
			var_implication = true;
		} else if (isTestImplied(test_var, test_dec, inode._var, false)) {
			var_implication = false;
		}
		//}

		// Check for implied branches before doing a full reduce on both branches
		if (var_implication == Boolean.TRUE) {

			ret = reduceLP(inode._high, test_var, test_dec);
		} else if (var_implication == Boolean.FALSE) {

			ret = reduceLP(inode._low, test_var, test_dec);

		} else {

			test_var.add(inode._var);
			test_dec.set(inode._var, false);
			int low = reduceLP(inode._low, test_var, test_dec);
			test_dec.set(inode._var, true);
			int high = reduceLP(inode._high, test_var, test_dec);
			test_dec.set(inode._var, null);
			test_var.remove(test_var.size() - 1);

			// Standard Reduce: getInode will handle the case of low == high
			ret = getINode(inode._var, low, high);
		}

		// Put return value in cache and return
		_hmReduceLPCache.put(new IntTriple(node_id, test_var.hashCode(), test_dec.hashCode()), ret);
		return ret;
	}


	// Checks cache for singleton decision variable implications or computes and caches 
	private boolean isSingleDecImplied(int par_dec, int child_dec) 
	{
		// See if implication already tested
		if (_mlImplications.contains(par_dec, child_dec)) {
			return true;
		} else if (_mlNonImplications.contains(par_dec, child_dec)) {
			return false;
		}

		// Otherwise, test and cache result
		boolean par_true = par_dec > 0;
		boolean child_true = child_dec > 0;
		int abs_par_dec = Math.abs(par_dec);
		int abs_child_dec = Math.abs(child_dec);


		ArrayList<Boolean> test_dec = new ArrayList<Boolean>();
		for (int i = 0; i < _alOrder.size(); i++) {
			test_dec.add(null);
		}

		// Looking at par_dec => child_dec (A=>B,A=>~B)

		test_dec.set(abs_par_dec, par_true);
		boolean test_implied = false;
		ArrayList<Integer> al_index2 = new ArrayList<Integer>(Arrays.asList(abs_par_dec));
		if (isTestImplied(al_index2, test_dec, abs_child_dec, child_true)) {
			_mlImplications.putValue(par_dec, child_dec);
			_mlImplications.putValue(-child_dec, -par_dec);
			test_implied =true;
		} else {
			_mlNonImplications.putValue(par_dec, child_dec);
			_mlNonImplications.putValue(-child_dec, -par_dec);				
		}

		///////////////////////////
		// adding other 3 implications: 
		// Looking at  child_dec => par_dec (B=>A , B=>~A , ~B=>A since ~B=>~A is pruned by consistency check)
		//just to add the implications to the list for redundancy checking
		test_dec = new ArrayList<Boolean>();
		for (int i = 0; i < _alOrder.size(); i++) {
			test_dec.add(null);
		}
		//only looking for B=>A 
		test_dec.set(abs_child_dec, child_true);
		ArrayList<Integer> al_index3 = new ArrayList<Integer>(Arrays.asList(abs_child_dec));
		if ((isTestImplied(al_index3, test_dec, abs_par_dec, par_true))) 
		{
			if (!_mlImplicationsChild.contains(child_dec, par_dec))
				_mlImplicationsChild.putValue(child_dec,par_dec);
			//only for intermediate implications, check if their disjunction is empty
			/*	if (Math.abs(child_dec - par_dec)>1)
				{
					if (!_mlIntermediate.contains(par_dec,child_dec))
						_mlIntermediate.putValue(par_dec,child_dec);
				}*/
		}
		//else if ((child_dec>0) &&(par_dec<0))
		// Looking at ~B=>A 
		test_dec.set(abs_child_dec, (!child_true));
		if ((isTestImplied(al_index3, test_dec, abs_par_dec, par_true)) )
		{
			if (!_mlImplicationsChild.contains(-child_dec, par_dec))
				_mlImplicationsChild.putValue(-child_dec,par_dec);
			/*if (Math.abs(child_dec + par_dec)>1)
				{
					if (!_mlIntermediate.contains(par_dec,-child_dec))
						_mlIntermediate.putValue(par_dec,-child_dec);
				}*/
			//_mlImplicationsChild.putValue(-par_dec,child_dec);
		} 
		// B=> ~A
		//	else if ((child_dec<0) &&(par_dec>0))
		//if (!_mlImplicationsChild.contains(-child_dec, par_dec))
		// Looking at not child_dec => par_dec  (~B=>A) 
		test_dec.set(abs_child_dec, child_true);
		//if (par_true == true) child_branch = child_dec;
		//else child_branch = -1 * child_dec;
		if ((isTestImplied(al_index3, test_dec, abs_par_dec, (!par_true))) )
		{
			if (!_mlImplicationsChild.contains(child_dec,-par_dec))
				_mlImplicationsChild.putValue(child_dec,-par_dec);
			/*if (Math.abs(child_dec + par_dec)>1)
					{
						if (!_mlIntermediate.contains(par_dec,child_dec))
							_mlIntermediate.putValue(par_dec,child_dec);
					}*/
			//_mlImplicationsChild.putValue(-par_dec,child_dec);
		}		
		//~B=>~A is redundant:
		/*test_dec.set(abs_child_dec, !child_true);
		//if (par_true == true) child_branch = child_dec;
		//else child_branch = -1 * child_dec;
		if ((isTestImplied(al_index3, test_dec, abs_par_dec, (!par_true))) )
		{
			if (!_mlImplicationsChild.contains(-child_dec,-par_dec))
				_mlImplicationsChild.putValue(-child_dec,-par_dec);
		}		*/
		//////////////////////////
		return test_implied;
	}

	private int reduceRedundancy(int tree, HashMap <Integer,ArrayList<ArrayList<Integer>>> formulas, PropKbCNF kb/*, HashMap<Integer,Boolean> marked_nodes*/) {
		Integer ret = null;
		XADDNode n = _hmInt2Node.get(tree);
		if (n == null) {
			System.out.println("ERROR: " + tree + " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		if (n instanceof XADDTNode) {
			return tree; // Assuming that to have a node id means canonical
		}
		//formulas contains the decision node id's of the parent; add new decision node to low/high branch
		else {
			XADDINode inode = (XADDINode) n;
			//Decision current_dec = _alOrder.get(inode._var);
			ArrayList<ArrayList<Integer>> path_list = formulas.get(tree);
			ArrayList<Integer> new_path = new ArrayList<Integer>();
			ArrayList<ArrayList<Integer>> new_path_list1 = new ArrayList<ArrayList<Integer>>();
			ArrayList<ArrayList<Integer>> new_path_list2 = new ArrayList<ArrayList<Integer>>();
			ArrayList<Integer> copy_new_path1 = new ArrayList<Integer>();
			ArrayList<Integer> copy_new_path2 = new ArrayList<Integer>();

			int high,low;
			//each parent may have different paths leading to it, perform this for all paths
			for (int i=0;i<path_list.size();i++)
			{
				new_path_list1 = new ArrayList<ArrayList<Integer>>();
				new_path_list2 = new ArrayList<ArrayList<Integer>>();
				new_path = path_list.get(i);
				copy_new_path1 = new ArrayList<Integer>();
				copy_new_path2 = new ArrayList<Integer>();
				copy_new_path1 = (ArrayList<Integer>) new_path.clone();
				copy_new_path2 = (ArrayList<Integer>) new_path.clone();
				copy_new_path1.add(inode._var);
				new_path_list1.add(copy_new_path1);
				if (formulas.containsKey(inode._high))
				{
					ArrayList<ArrayList<Integer>> h_child_path = formulas.get(inode._high);
					h_child_path.add(copy_new_path1);
				}
				else formulas.put(inode._high,new_path_list1);
				copy_new_path2.add(-(inode._var));
				new_path_list2.add(copy_new_path2);
				if (formulas.containsKey(inode._low))
				{
					ArrayList<ArrayList<Integer>> l_child_path = formulas.get(inode._low);
					l_child_path.add(copy_new_path2);
				}
				else formulas.put(inode._low,new_path_list2);
			}

			high = reduceRedundancy(inode._high, formulas,kb);
			low = reduceRedundancy(inode._low, formulas,kb);

			//after all the tree has been checked for child-parent implications,
			//now at each inode, test to see if the false or true branch can be removed 
			//if low branch can be removed, then (the formula of true branch = formula) 
			if (isTestSAT(inode._var, true, formulas.get(low), kb))
			{
				//return correct branch which is the opposite of the returned node
				return high;
			}
			else if (isTestSAT(inode._var, false, formulas.get(high),kb))
			{
				return low;
			}

			else
			{
				ret = getINode(inode._var, low, high);
			}
		}

		return ret;
	}


	private boolean isTestSAT(int _var, boolean b, ArrayList<ArrayList<Integer>> paths, PropKbCNF kb) 
	{
		//KB contains conjunction of all implications: child => parent , child =>~parent , parent=>child
		//next build query: first build formula of F, put it equal to F(var=b)
		//build F
		if (paths == null) 
			return false;
		if (paths.size()<2) return false;
		String f = "((";
		for (int i=0;i<paths.size();i++)
		{
			ArrayList<Integer> singlePath = paths.get(i);
			f = f.concat("(");
			for (int j=0;j<singlePath.size()-1;j++)
			{
				//don't add root node parent
				if (singlePath.get(j)!= 0)
				{
					if (singlePath.get(j)<0)
						f =  f.concat(" ~a"+Math.abs(singlePath.get(j))+"a ^ ");
					else f =  f.concat(" a"+singlePath.get(j)+"a ^ ");
				}
			}
			//last element
			if (singlePath.get(singlePath.size()-1)<0)
				f =  f.concat(" ~a"+Math.abs(singlePath.get(singlePath.size()-1))+"a ");
			else f =  f.concat(" a"+(singlePath.get(singlePath.size()-1))+"a ");
			f =  f.concat(")");

			if (i!=paths.size()-1) 
				f= f.concat(" | ");
		}
		f= f.concat(")");
		//build F(_var=b)
		String f_var = "(";
		for (int i=0;i<paths.size();i++)
		{
			ArrayList<Integer> singlePath = paths.get(i);
			f_var = f_var.concat("(");
			for (int j=0;j<singlePath.size()-1;j++)
			{
				//don't add root node parent
				if (singlePath.get(j)!=0)
				{
					if (Math.abs(singlePath.get(j))==_var)
					{
						if (singlePath.get(j)<0)
						{
							if (b) f_var = f_var.concat(" false ^");
							else f_var = f_var.concat(" true ^");
						}
						else 
						{
							if (b) f_var = f_var.concat(" true ^");
							else f_var = f_var.concat(" false ^");
						}
					}
					else 
					{
						if (singlePath.get(j)<0)
							f_var = f_var.concat(" ~a"+Math.abs(singlePath.get(j))+"a ^ ");
						else f_var = f_var.concat(" a"+singlePath.get(j)+"a ^ ");
					}
				}
			}
			//last element
			if (Math.abs(singlePath.get(singlePath.size()-1))==_var)
			{
				if (singlePath.get(singlePath.size()-1)<0)
				{
					if (b) f_var = f_var.concat(" false ");
					else f_var = f_var.concat(" true ");
				}
				else 
				{
					if (b) f_var = f_var.concat(" true ");
					else f_var = f_var.concat(" false ");
				}
			}
			else 
			{
				if (singlePath.get(singlePath.size()-1)<0)
					f_var = f_var.concat(" ~a"+Math.abs(singlePath.get(singlePath.size()-1))+"a ");
				else f_var = f_var.concat(" a"+(singlePath.get(singlePath.size()-1))+"a ");
			}

			f_var = f_var.concat(")");

			if (i!=paths.size()-1) f_var = f_var.concat(" | ");
		}
		f_var = f_var.concat(")");

		//SAT test
		f = f.concat(" => ");
		f = f.concat(f_var+")");

		//System.out.println(f + ": " + (kb.querySATSolver(f) ? "entailed" : "not entailed"));
		if (kb.querySATSolver(f))
			return true;
		else
			return false;
	}

	public void ensureCVarIDsUpToDate() {

		/*if (_cvar2ID.size() == _hmContinuousVars.size())
			return;

		_cvar2ID.clear();
		for (int id = 0; id < _hmContinuousVars.size(); id++)
			_cvar2ID.put(_hmContinuousVars.get(id), id);*/
		if (_cvar2ID.size() == _alContinuousVars.size())
			return;

		_cvar2ID.clear();
		for (int id = 0; id < _alContinuousVars.size(); id++)
			_cvar2ID.put(_alContinuousVars.get(id), id);
	}

	private boolean isTestImplied(ArrayList<Integer> test_var,
			ArrayList<Boolean> test_dec, int var_id, boolean dec) {

		if (test_var.size() == 0)
			return false;

		if (DEBUG_CONSTRAINTS) {
			System.out.println("===================\nisTestImplied: "+ _alOrder.get(var_id) + " = " + dec);
			for (int cons : test_var) {
				System.out.println("- cons :: " + _alOrder.get(cons) + " = "
						+ test_dec.get(cons));
			}
		}

		// if (a > b + c) == true makes system infeasible then it must be
		// implied
		// that (a > b + c) == false (prove A => B by seeing if A^~B is
		// infeasible)

		// Setup LP
		ensureCVarIDsUpToDate();
		int nvars = _cvar2ID.size();
		double[] obj_coef = new double[nvars]; // default all zeros, which is
		// what we want
		double[] lb = new double[nvars];
		double[] ub = new double[nvars];
		for (Map.Entry<String, Integer> me : _cvar2ID.entrySet()) {
			String cvar = me.getKey();
			Integer cvar_id = me.getValue();
			Double d_lb = this._hmMinVal.get(cvar);
			lb[cvar_id] = d_lb != null ? d_lb : -1e10d;
			Double d_ub = this._hmMaxVal.get(cvar);
			ub[cvar_id] = d_ub != null ? d_ub : 1e10d;
			obj_coef[cvar_id] = 1d;
		}

		LP lp = new LP(nvars, lb, ub, obj_coef, LP.MAXIMIZE);

		// Now add all constraints
		for (Integer constraint_id : test_var) {
			addConstraint(lp, constraint_id, test_dec.get(constraint_id));
		}

		// Finally add the negated decision to test
		addConstraint(lp, var_id, !dec);

		// Solve and get decision
		double[] soln = lp.solve();
		boolean implied = (lp._status == LpSolve.INFEASIBLE);
		if (DEBUG_CONSTRAINTS)
			System.out.println("Solution: " + LP.PrintVector(lp._x));
		lp.free();

		// Since dec inverted, infeasibility implies that the implication is
		// true
		// System.out.println("- RESULT: " + implied);
		return implied;
	}

	private void addConstraint(LP lp, int constraint_id, boolean dec) {

		if (DEBUG_CONSTRAINTS)
			System.out.println("Adding constraint id [" + constraint_id
					+ "] = " + dec);

		Decision d = _alOrder.get(constraint_id);
		if (d instanceof ExprDec) {
			ExprDec e = (ExprDec) d;
			/*if (!(e._expr._rhs instanceof DoubleExpr)
					|| ((DoubleExpr) e._expr._rhs)._dConstVal != 0d) {
				System.out.println("WARNING: Unexpected RHS constraint value: "
						+ e._expr._rhs);*/
			// take these out so it does not terminal upon bilinear
			// decisions
			// new Exception().printStackTrace(System.out);
			// System.exit(1);
			//}
			// From here we just need convert LHS to coefficients and construct
			// correct constraint from CompExpr type
			double[] coefs = new double[_cvar2ID.size()];

			try {
				double const_coef = setCoefficients(e._expr._lhs, coefs); // move
				// to
				// RHS
				// =>
				// -

				int type = dec ? e._expr._type : invertType(e._expr._type);

				if (DEBUG_CONSTRAINTS)
					System.out.println("- adding cons: " + const_coef + " + "
							+ LP.PrintVector(coefs) + " <=> "
							+ (dec ? "" : "!") + e._expr);

				switch (type) {
				case GT:
					lp.addGTConstraint(coefs, -const_coef);
					break;
				case GT_EQ:
					lp.addGeqConstraint(coefs, -const_coef);
					break;
				case LT:
					lp.addLTConstraint(coefs, -const_coef);
					break;
				case LT_EQ:
					lp.addLeqConstraint(coefs, -const_coef);
					break;
				case EQ:
					lp.addEqConstraint(coefs, -const_coef);
					break;
				case NEQ:
					break; // Can't add an NEQ constraint
				default:
					break; // Unknown constraint type
				}
			} catch (Exception e2) {
				System.err.println("Could not add constraint: " + e2
						+ "\n... skipping");
			}
		}
	}

	private int invertType(int type) {
		switch (type) {
		case GT:
			return LT_EQ;
		case GT_EQ:
			return LT;
		case LT:
			return GT_EQ;
		case LT_EQ:
			return GT;
		case EQ:
			return NEQ;
		case NEQ:
			return EQ;
		default:
			return -1; // Unknown constraint type
		}
	}

	// Convert an expression to an array of coefficients and a constant
	private double setCoefficients(ArithExpr e, double[] coefs)
			throws Exception {

		int error = 0;
		int index = 0;
		double accum = 0d;
		if (e instanceof OperExpr) {
			OperExpr o = ((OperExpr) e);
			if (o._type == PROD) {
				if (o._terms.size() != 2)
					error = 1;
				else {
					index = _cvar2ID.get(((VarExpr) o._terms.get(1))._sVarName);
					coefs[index] = ((DoubleExpr) o._terms.get(0))._dConstVal;
				}
			} else if (o._type == SUM) {
				for (ArithExpr e2 : o._terms)
					accum += setCoefficients(e2, coefs);
			} else
				error = 2;
		} else if (e instanceof DoubleExpr) {
			accum += ((DoubleExpr) e)._dConstVal;
		} else
			error = 3;

		if (error > 0) {
			System.out.println("[" + error
					+ "] Unexpected LHS constraint term: " + e);
			throw new Exception("[" + error
					+ "] Unexpected LHS constraint term: " + e); // .printStackTrace(System.out);
			// System.exit(1);
		}

		return accum;
	}

	/*public int makeCanonical(int node_id,boolean flush) {
		// Graph g = getGraph(node_id);
		// g.addNode("_temp_");
		// g.addNodeLabel("_temp_", "Before make canonical");
		// g.addNodeShape("_temp_", "square");
		// g.addNodeStyle("_temp_", "filled");
		// g.addNodeColor("_temp_", "lightblue");
		// g.launchViewer(1300, 770);
		if (flush) flushCaches();
		return reduceSub(node_id, new HashMap<String, ArithExpr>(),
				new HashMap<Integer, Integer>());

	}*/
	public int makeCanonical(int node_id) {
		// Graph g = getGraph(node_id);
		// g.addNode("_temp_");
		// g.addNodeLabel("_temp_", "Before make canonical");
		// g.addNodeShape("_temp_", "square");
		// g.addNodeStyle("_temp_", "filled");
		// g.addNodeColor("_temp_", "lightblue");
		// g.launchViewer(1300, 770);
		//flushCaches();
		int ret =  reduceSub(node_id, new HashMap<String, ArithExpr>(),
				new HashMap<Integer, Integer>());
		_hsSpecialNodes.add(ret);
		flushCaches();
		return ret;
	}

	// Not worrying about reusing cache across class
	// TODO: substitution has to enforce order if it is violated
	public int substitute(int node_id, HashMap<String, ArithExpr> subst) {
		return reduceSub(node_id, subst, new HashMap<Integer, Integer>());
	}

	// TODO: substitution has to enforce order if it is violated
	// could possibly do with a pairwise reordering...
	public int reduceSub(int node_id, HashMap<String, ArithExpr> subst,
			HashMap<Integer, Integer> subst_cache) {

		Integer ret = null;
		XADDNode n = _hmInt2Node.get(node_id);
		if (n == null) {
			System.out.println("ERROR: " + node_id
					+ " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		// by default if hashing and equality testing are working in getTNode
		DoubleExpr zeroVal = new DoubleExpr(0);
		if (n instanceof XADDTNode) {
			ArithExpr expr = ((XADDTNode)n)._expr.substitute(subst);
			Object annotation = ((XADDTNode)n)._annotate;
			if (annotation != null && annotation instanceof ArithExpr) {
				annotation = ((ArithExpr)annotation).substitute(subst);
			}
			return getTermNode(expr, annotation);
		}

		// If its an internal node, check the reduce cache
		if ((ret = subst_cache.get(node_id)) != null) {
			// System.out.println("In cache, returning: " + qret);
			return ret;
		}

		// Handle an internal node
		XADDINode inode = (XADDINode) n;

		int low = reduceSub(inode._low, subst, subst_cache);
		int high = reduceSub(inode._high, subst, subst_cache);

		int var = inode._var;
		Decision d = _alOrder.get(var);
		if (d instanceof ExprDec) {
			// Only need to substitute if a var expression
			CompExpr comp = ((ExprDec) d)._expr;
			comp = comp.substitute(subst);
			d = new ExprDec(comp);
			var = getVarIndex(d, true);
		} else if (d instanceof BoolDec) {
			// System.out.println(((BoolDec)d)._sVarName + ": " + subst);
			VarExpr sub = (VarExpr) subst.get(((BoolDec) d)._sVarName);
			if (sub != null) {
				// There is a substitution for this BoolDec... get new var index
				var = getVarIndex(new BoolDec(sub._sVarName), false);
			}
		}

		// Getting an Inode directly can be unsafe due to the fact that a
		// substitution could have affected a variable reordering...
		// uglier and more computationally costly, but the better solution
		// is via apply.
		//
		// ret = getINode(var, low, high);\
		int T_ZERO, T_ONE;
		/*
		 * if (ANNOTATE_ENABLE) { T_ZERO =
		 * getTermNode(ZERO,ArithExpr.parse("0")); T_ONE =
		 * getTermNode(ONE,ArithExpr.parse("0")); }else
		 */
		T_ZERO = getTermNode(ZERO);
		T_ONE = getTermNode(ONE);
		int ind_true = getINode(var, /* low */T_ZERO, /* high */T_ONE);
		int ind_false = getINode(var, /* low */T_ONE, /* high */T_ZERO);
		int true_half = applyInt(ind_true, high, PROD); // Note: this
		// enforces
		// canonicity so
		int false_half = applyInt(ind_false, low, PROD); // can use applyInt
		// rather than
		// apply
		ret = applyInt(true_half, false_half, SUM);
		if (CHECK_LOCAL_ORDERING) {
			// Check ordering
			XADDNode new_node = _hmInt2Node.get(ret);
			if (new_node instanceof XADDINode) {
				XADDINode new_inode = (XADDINode) new_node;
				int var_id = new_inode._var;
				XADDNode low_n = _hmInt2Node.get(new_inode._low);
				if (low_n instanceof XADDINode) {
					XADDINode low_ni = (XADDINode) low_n;
					if (var_id > low_ni._var) {
						System.out.println("Reordering problem: " + var_id+ " > " + low_ni._var);
						System.out.println(var_id + ": " + _alOrder.get(var_id));
						System.out.println(low_ni._var + ": "+ _alOrder.get(low_ni._var));
						new Exception().printStackTrace(System.out);
						// System.exit(1);
					}
				}
				XADDNode high_n = _hmInt2Node.get(new_inode._high);
				if (high_n instanceof XADDINode) {
					XADDINode high_ni = (XADDINode) high_n;
					if (var_id > high_ni._var) {
						System.out.println("Reordering problem: " + var_id	+ " > " + high_ni._var);
						System.out.println(var_id + ": " + _alOrder.get(var_id));
						System.out.println(high_ni._var + ": "+ _alOrder.get(high_ni._var));
						new Exception().printStackTrace(System.out);
						// System.exit(1);
					}
				}
			}
		}

		// Put return value in cache and return
		subst_cache.put(node_id, ret);
		return ret;
	}

	// ///////////

	// Convert an ArithExpr to an XADD while performing (optional) substitution
	// of
	// an XADD for a var (set var = null if no substitution is needed)
	public int substituteXADDforVarInArithExpr(ArithExpr leaf_val, String var,
			int xadd) {
		if (leaf_val instanceof OperExpr) {
			OperExpr oper_expr = (OperExpr) leaf_val;
			int running_xadd = substituteXADDforVarInArithExpr(
					oper_expr._terms.get(0), var, xadd);
			for (int i = 1; i < oper_expr._terms.size(); i++) {
				int next_operand = substituteXADDforVarInArithExpr(
						oper_expr._terms.get(i), var, xadd);
				_hsSpecialNodes.add(running_xadd);
				running_xadd = apply(running_xadd, next_operand,
						oper_expr._type /* SUM, PROD, ... */);
			}
			return running_xadd;
		} else if (leaf_val instanceof VarExpr) {
			VarExpr var_expr = (VarExpr) leaf_val;
			if (var_expr._sVarName == var) // assume interned
			{

				return xadd;
			} else
				return getTermNode(leaf_val);
		} else if (leaf_val instanceof DoubleExpr) {
			return getTermNode(leaf_val);
		} else {
			System.out.println("substituteXADDforVar: Unsupported expression '"	+ leaf_val + "'");
			System.exit(1);
			return -1;
		}
	}

	public Double evaluate(int node_id, HashMap<String, Boolean> bool_assign, HashMap<String, Double> cont_assign) {

		// Get root
		XADDNode n = _hmInt2Node.get(node_id);

		// Traverse decision diagram until terminal found
		while (n instanceof XADDINode) {
			XADDINode inode = (XADDINode) n;
			Decision d = _alOrder.get(inode._var);
			Boolean branch_high = null;
			if (d instanceof TautDec)
				branch_high = ((TautDec) d)._bTautology;
			else if (d instanceof BoolDec)
				branch_high = bool_assign.get(((BoolDec) d)._sVarName);
			else if (d instanceof ExprDec) {
				branch_high = ((ExprDec) d)._expr.evaluate(cont_assign);
				if (SHOW_DECISION_EVAL) {
					System.out.println(" - " + ((ExprDec) d)._expr + ": " + branch_high);
				}
			}

			// Not all required variables were assigned
			if (branch_high == null)
				return null;

			// Advance down to next node
			n = _hmInt2Node.get(branch_high ? inode._high : inode._low);
		}

		// Now at a terminal node so evaluate expression
		XADDTNode t = (XADDTNode) n;
		return t._expr.evaluate(cont_assign);
	}

	// TODO: could an op other than max/min lead to a non-canonical diagram???
	// only ops that can change inodes can affect ordering and the only
	// ops that can do this should be max/min.
	public int scalarOp(int dd, double val, int op) {
		int dd_val = getTermNode(new DoubleExpr(val));
		return apply(dd, dd_val, op); // could make non-canonical so have to use apply
	}

	/*	public Double evaluate_policy(int node_id,
	HashMap<String, Boolean> bool_assign,
	HashMap<String, Double> cont_assign) {

// Get root
XADDNode n = _hmInt2Node.get(node_id);

// Traverse decision diagram until terminal found
while (n instanceof XADDINode) {
	XADDINode inode = (XADDINode) n;
	Decision d = _alOrder.get(inode._var);
	Boolean branch_high = null;
	if (d instanceof TautDec)
		branch_high = ((TautDec) d)._bTautology;
	else if (d instanceof BoolDec)
		branch_high = bool_assign.get(((BoolDec) d)._sVarName);
	else if (d instanceof ExprDec) {
		branch_high = ((ExprDec) d)._expr.evaluate(cont_assign);
		if (SHOW_DECISION_EVAL) {
			//System.out.println(" - " + ((ExprDec) d)._expr + ": "	+ branch_high);
		}
	}

	// Not all required variables were assigned
	if (branch_high == null)
		return null;

	// Advance down to next node
	n = _hmInt2Node.get(branch_high ? inode._high : inode._low);
}

// Now at a terminal node so evaluate expression
//
XADDTNode t = (XADDTNode) n;
if (t._annotate_action == null)
	t._annotate_action = "";
if (t._annotate == null)
	t._annotate = new DoubleExpr(0);
if (t._annotate_action.contains("no"))
	return (-1 * t._annotate.evaluate(cont_assign));
else
	return t._annotate.evaluate(cont_assign);
}*/


	public IntTriple _tempApplyKey = new IntTriple(-1, -1, -1);

	// TODO: could an op other than max/min lead to a non-canonical diagram???
	// only ops that can change inodes can affect ordering and the only
	// ops that can do this should be max/min.
	public int apply(int a1, int a2, int op) {
		lastDecision.clear();
		// start with no divisions, i4 = -1
		int ret = applyInt(a1, a2, op);
		// TODO: should maintain a reusable reduce cache here
		return makeCanonical(ret);
	}

	public int applyInt(int a1, int a2, int op) {

		// adding divBranch, -1 if no divison, 1 if branch false, 2 if branch
		// true
		_tempApplyKey.set(a1, a2, op);
		Integer ret = _hmApplyCache.get(_tempApplyKey);
		if (ret != null) {
			return ret;
		}

		// Can we create a terminal node here?
		XADDNode n1 = _hmInt2Node.get(a1);
		XADDNode n2 = _hmInt2Node.get(a2);
		ret = computeTermNode(a1, n1, a2, n2, op);
		if (ret == null) {

			int v1low, v1high, v2low, v2high, var;

			// Find node with min id (or only internal node)
			if (n1 instanceof XADDINode) {
				if (n2 instanceof XADDINode) {
					if (((XADDINode) n1)._var < ((XADDINode) n2)._var) {
						var = ((XADDINode) n1)._var;
					} else {
						var = ((XADDINode) n2)._var;
					}
				} else {
					var = ((XADDINode) n1)._var;
				}
			} else {
				var = ((XADDINode) n2)._var;
			}

			// Determine next recursion for n1
			if ((n1 instanceof XADDINode) && (((XADDINode) n1)._var == var)) {
				XADDINode n1i = (XADDINode) n1;
				v1low = n1i._low;
				v1high = n1i._high;
			} else {
				v1low = a1;
				v1high = a1;
			}

			// Determine next recursion for n2
			if ((n2 instanceof XADDINode) && (((XADDINode) n2)._var == var)) {
				XADDINode n2i = (XADDINode) n2;
				v2low = n2i._low;
				v2high = n2i._high;
			} else {
				v2low = a2;
				v2high = a2;
			}

			// Perform in-line reduction and set min/max for subnodes if needed
			int low = applyInt(v1low, v2low, op);
			int high = applyInt(v1high, v2high, op);

			// getINode will take care of 'low==high'
			ret = getINode(var, low, high);

		}

		_hmApplyCache.put(new IntTriple(a1, a2, op), ret);
		return ret;
	}

	// Computes a terminal node value if possible, assume
	// terms of same type (otherwise incompatible!)
	public Integer computeTermNode(int a1, XADDNode n1, int a2, XADDNode n2,
			int op) {

		changed_var_index = -1;
		if ((n1 instanceof XADDTNode) && (n2 instanceof XADDTNode)) 
		{
			XADDTNode xa1 = (XADDTNode) n1;
			XADDTNode xa2 = (XADDTNode) n2;

			if ((op != MAX) && (op != MIN)) {
				 return getTermNode(new OperExpr(op, xa1._expr, xa2._expr));

			}
			ArithExpr diff = new OperExpr(MINUS, xa1._expr, xa2._expr);
			CompExpr comp = null;
			if (USE_MINUS_COMP)
				comp = new CompExpr(LT, diff, new DoubleExpr(0d));
			else
				comp = new CompExpr(LT_EQ, xa1._expr, xa2._expr);

			// TODO: Remove
			//System.out.println("**ON MAX: " + xa1._expr + " <= " + xa2._expr);
			//System.out.println("**ON MAX, After simplification: "	+ comp.makeCanonical());

			// STEP1: For actions changed this!
			// comp = new CompExpr(GT_EQ, xa1._expr, xa2._expr);

			Decision d = new ExprDec(comp);

			// Do a range check here
			// if (CHECK_MIN_MAX) {
			// TautDec tdec = checkRangeImpliedDecision(d);
			// if (tdec != null)
			// d = tdec; // Change to a tautology... getInode will handle this
			// }
			// makes decisions canonical here!!!!!!!!!!!!
			int var_index = getVarIndex(d, true);
			// last node had a division
			
			// System.out.println("ComputeTerm::max var_index " +
			// _alOrder.get(var_index) + ": " + comp);
			// System.exit(1);

			int node1, node2;
			node1 = getTermNode(xa1._expr);
			node2 = getTermNode(xa2._expr);

			// STEP2: change this for actions too
			return getINode(var_index, op == MAX ? node1 : node2,
					op == MAX ? node2 : node1);
			// return getINode(var_index, op == MAX ? node2 : node1, op == MAX ?
			// node1 : node2);
		}

		if (n1 instanceof XADDTNode) {
			// If we get here a2 must be XADDINode
			XADDTNode xa1 = (XADDTNode) n1;

			// Check for identity operation value for n1
			if ((op == SUM && xa1._expr.equals(ZERO))
					|| (op == PROD && xa1._expr.equals(ONE))) {
				return a2;
			}
		}

		if (n2 instanceof XADDTNode) {
			// If we get here a1 must be XADDINode
			XADDTNode xa2 = (XADDTNode) n2;

			// Check for identity operation value for n2
			if ((op == SUM && xa2._expr.equals(ZERO))
					|| (op == PROD && xa2._expr.equals(ONE))
					|| (op == MINUS && xa2._expr.equals(ZERO))
					|| (op == DIV && xa2._expr.equals(ONE))) {
				return a1;
			}
		}

		return null;
	}
	
	// Quick cache snapshot
		public void showCacheSize() {
			System.out.println("APPLY CACHE:    " + _hmApplyCache.size());
			System.out.println("REDUCE CACHE:   " + _hmReduceCache.size());
			System.out.println("REDUCE CACHE L: " + _hmReduceLeafOpCache.size());
			System.out.println("REDUCE CACHE A: " + _hmReduceAnnotateCache.size());
			System.out.println("INODE CACHE 1:  " + _hmNode2Int.size() + "\n");		 
			System.out.println("INODE CACHE 2:  " + _hmInt2Node.size() + "\n");
			System.out.println("VAR CACHE 2:    " + _hmINode2Vars.size() + "\n");
		}

		public void clearMarks() {
			_markCounter++;
		}

	/////////////////////////////////////////////////////////////////////////////////////
	//                               XADD Leaf Operations
	//
	// - maximization of a variable (max_v F(v))  
	// - integration (int_v F(v)... indefinite and definite) 
	// - differentiation (partial_v / partial_F F(v))
	// - XADD substitution for a variable (int_v delta(v - G)*F = F{v/G})
	//   ... for now, v can only occur a leaves of F, but can generalize to any F
	//
	/////////////////////////////////////////////////////////////////////////////////////

	// This internal class is intended to be used to specify inline operations to perform at the
	// leaves of an XADD... the operation returns a new XADD for the leaf.
	//
	// 'decisions' and 'decision_values' are parallel arrays indicating the path taken to 'leaf_val'
	// 'xadd' is the XADD being subsituted for 'var'
	public abstract class XADDLeafOperation {
		public abstract int processXADDLeaf(ArrayList<Decision> decisions,
				ArrayList<Boolean> decision_values, ArithExpr leaf_val);

		public abstract boolean isCacheable();
	}

////////////////////////////////////////////////////////////////////////////////
// XADDLeafMax added by Zahra 
// Class of XADDLeafMax that preforms max over a variable on the leaves subject
// to the constraints encountered to reach those leaves.  The leaf max is over
// the LB,UB or any root of the polynomial.
////////////////////////////////////////////////////////////////////////////////

	public class XADDLeafMaxMin extends XADDLeafOperation {

		public int _runningMaxMin; // XADD for the running max of all leaf substitutions
		double _lowerBound, _upperBound;
		String _maxMinVar;
		PrintStream _log = null;
		boolean isMax =true;
		
		public XADDLeafMaxMin(String max_var, double lower_bound, double upper_bound, boolean max, PrintStream ps) 
		{
			isMax = max;
			_maxMinVar = max_var.intern(); 
			_lowerBound = lower_bound;
			_upperBound = upper_bound;
			if (isMax) _runningMaxMin = -1;
			else _runningMaxMin = getTermNode(POS_INFINITE);
			_log = ps;
		}


		// TODO: revisit whether caching is possible, or in what circumstances
		public boolean isCacheable() {
			return false;
		}

		public int processXADDLeaf(ArrayList<Decision> decisions, ArrayList<Boolean> decision_values, ArithExpr leaf_val) 
		{
			// Bound management
			ArrayList<ArithExpr> lower_bound = new ArrayList<ArithExpr>();
			ArrayList<ArithExpr> upper_bound = new ArrayList<ArithExpr>();
			
			
			// Multiply these in later
			HashMap<Decision, Boolean> var_indep_decisions = new HashMap<Decision, Boolean>();

			// First compute the upper and lower bounds and var-independent constraints
			// from the decisions
			for (int i = 0; i < decisions.size(); i++) 
			{
				Decision d = decisions.get(i);
				Boolean is_true = decision_values.get(i);
				CompExpr comp = null;
				if (d instanceof BoolDec) {
					var_indep_decisions.put(d, is_true);
					continue;
				} else if (d instanceof ExprDec) {
					ExprDec ed = (ExprDec) d;
					comp = ed._expr;
				} else {
					//_log.println("processXADDLeaf: Unsupported decision type '" + d + "'");
					System.exit(1);
				}

				// Check that comparison expression is normalized
				if (!comp._rhs.equals(ZERO)) {
					//_log.println("processXADDLeaf: Expected RHS = 0 for '" + comp + "'");
					System.exit(1);
				}
				// Takes ArithExpr expr1 linear in var, returns (coef,expr2) where expr1 = coef*x + expr2
				CoefExprPair p = comp._lhs.removeVarFromExpr(_maxMinVar); 
				ArithExpr lhs_isolated = p._expr;
				double    var_coef     = p._coef;
				//_log.println("Pre: " + comp + " == " + is_true + ", int var [" + _maxVar + "]"
						//+ "\nLHS isolated: " + lhs_isolated + "\n ==>  " + var_coef + " * " + _maxVar);

				if (var_coef == 0d) {
					var_indep_decisions.put(d, is_true);
					continue;
				}

				// We have var_coef*x + lhs_isolated {<,<=,>,>=} 0
				// ... need to get x {<,<=,>,>=} 1/var_coef * lhs_isolated
				//     (and inequality gets flipped if var_coef is negative)
				boolean flip_comparison = (var_coef < 0d) && (comp._type != EQ) && (comp._type != NEQ);
				ArithExpr new_rhs = (ArithExpr) new OperExpr(MINUS, ZERO, new OperExpr(PROD, new DoubleExpr(
						1d / var_coef), lhs_isolated)).makeCanonical();

				// Divide through by coef (pos or neg)
				// - if coef neg, flip expression
				// - if decision neg, flip expression
				// - if both, don't flip
				int comp_oper = comp._type;
				if ((/* negated */!is_true && !flip_comparison) || (/* not negated */is_true && flip_comparison)) {
					comp_oper = CompExpr.flipCompOper(comp_oper);
				}

				// Now we have (x {<,<=,>,>=} expr)... mark each as lower/upper bound:
				// - lower bounds: x > f(y), x >= f(y)
				// - upper bounds: x < f(z), x <= f(z)
				if (comp_oper == GT || comp_oper == GT_EQ)
					lower_bound.add(new_rhs);
				else if (comp_oper == LT || comp_oper == LT_EQ)
					upper_bound.add(new_rhs);
				else {
					//_log.println("Cannot currently handle: "
							//+ new CompExpr(comp_oper, new VarExpr(_maxVar), new_rhs));
					//_log.println("Note: = triggers substitution, not sure how to handle ~=");
					new Exception().printStackTrace();
					System.exit(1);
				}
			}

			// Now explicitly compute lower and upper bounds as XADDs
			// If these are polynomials, must go to +/- infinity at limits so cannot
			// be used to approximate cdfs. Hence we must assume that there will always
			// be limits on the polynomial functions implicit in the bounds.
			//_log.println("Lower bounds: " + lower_bound);
			//this way does not add constraints of default bounds! 
			int xadd_lower_bound=-1, xadd_upper_bound=-1;
			if (lower_bound.isEmpty() && xadd_lower_bound == -1) {
				xadd_lower_bound = getTermNode(new DoubleExpr(_lowerBound));
			} else {
				for (ArithExpr e : lower_bound) {
					if (xadd_lower_bound == -1) {
						xadd_lower_bound = getTermNode(e);
					} else {
						xadd_lower_bound = apply(xadd_lower_bound,getTermNode(e), MAX);
					}
				}
			}

			if (upper_bound.isEmpty() && xadd_upper_bound == -1) {
				xadd_upper_bound = getTermNode(new DoubleExpr(_upperBound));
			} else {
				for (ArithExpr e : upper_bound) {
					if (xadd_upper_bound == -1) {
						xadd_upper_bound = getTermNode(e);
					} else {
						 xadd_upper_bound = apply(xadd_upper_bound,	getTermNode(e), MIN);
					}
				}
			}
					
/*			int xadd_lower_bound = -1;
			if (lower_bound.size()==0) lower_bound.add(new DoubleExpr(_lowerBound));
			for (ArithExpr e : lower_bound) // Lower bound is max of all lower bounds
					xadd_lower_bound = (xadd_lower_bound == -1) ? getTermNode(e): apply(xadd_lower_bound, getTermNode(e), MAX);
			int xadd_upper_bound = -1;
			if (upper_bound.size()==0) upper_bound.add(new DoubleExpr(_upperBound));
			for (ArithExpr e : upper_bound) // Upper bound is min of all upper bounds
					xadd_upper_bound = (xadd_upper_bound == -1) ? getTermNode(e): apply(xadd_upper_bound, getTermNode(e), MIN);*/

			// Build all constraints for the maximization
			//NOTE: don't add constraints for default bounds 
			for (ArithExpr e1 : upper_bound) {
				for (ArithExpr e2 : lower_bound) {
					CompExpr ce = new CompExpr(GT, e1, e2);
					ExprDec ed = new ExprDec(ce);
					var_indep_decisions.put(ed, Boolean.TRUE);
				}
			}

			// Display lower and upper bounds
			//_log.println("** Lower bound:\n" + getString(xadd_lower_bound));
			//_log.println("** Upper bound:\n" + getString(xadd_upper_bound));

			// Determine whether we need to handle the quadratic case, if so,
			// root will be set to a non-null evaluation
			ArithExpr root = null;
			int highest_order = leaf_val.determineHighestOrderOfVar(_maxMinVar);
			if (highest_order > 2) {
				//_log.println("XADDLeafMax: Cannot currently handle expressions higher than order 2 in " + _maxVar + ": " + leaf_val);
				System.exit(1);					
			} else if (highest_order == 2) {
				ArithExpr first_derivative = leaf_val.differentiateExpr(_maxMinVar);

				// Takes ArithExpr expr1 linear in var, returns (coef,expr2) where expr1 = coef*x + expr2
				// setting expr1 = coef*x + expr2 = 0 then x = -expr2/coef
				CoefExprPair p2 = first_derivative.removeVarFromExpr(_maxMinVar);

				root = (ArithExpr)(new OperExpr(MINUS, ZERO, new OperExpr(PROD, new DoubleExpr(
						1d / p2._coef), p2._expr)).makeCanonical());
			}
			
			// Substitute lower and upper bounds into leaf
			int _eval_lower = substituteXADDforVarInArithExpr(leaf_val, _maxMinVar, xadd_lower_bound);
			int _eval_upper = substituteXADDforVarInArithExpr(leaf_val, _maxMinVar, xadd_upper_bound);
			// need these for annotation, since the UB,LB are canonical!
			//_hsSpecialNodes.add(max_eval_upper);
			//_hsSpecialNodes.add(max_eval_lower);
			_eval_upper = makeCanonical(_eval_upper);
			_eval_lower = makeCanonical(_eval_lower);
			
			int maxMin_eval;
			if (isMax)
				maxMin_eval = apply(_eval_upper, _eval_lower, MAX);
			else maxMin_eval = apply(_eval_upper, _eval_lower, MIN);
			maxMin_eval = reduceLinearize(maxMin_eval); 
			maxMin_eval = reduceLP(maxMin_eval); 
			//_hsSpecialNodes.add(max_eval);
			maxMin_eval = makeCanonical(maxMin_eval);
			

			// NOTE: Constraints on root have to be multiplied in here, not at end.  -Scott
			if (root != null) {

				int _eval_root = substituteXADDforVarInArithExpr(leaf_val, _maxMinVar, getTermNode(root));
				//_log.println("root substitute: " + getString(max_eval_root));

				// Now multiply in constraints into int_eval, make result canonical
				for (ArithExpr ub : upper_bound) {
					CompExpr ce = new CompExpr(LT_EQ, root, ub);
					int ub_xadd = getVarNode(new ExprDec(ce), 0d, 1d);
					_eval_root = apply(_eval_root, ub_xadd, PROD);
				}
				for (ArithExpr lb : lower_bound) {
					CompExpr ce = new CompExpr(GT, root, lb);
					int lb_xadd = getVarNode(new ExprDec(ce), 0d, 1d);
					_eval_root = apply(_eval_root, lb_xadd, PROD);
				}
				_eval_root = reduceLinearize(_eval_root); 
				_eval_root = reduceLP(_eval_root); // Result should be canonical

				//_log.println("constrained root substitute: " + getString(max_eval_root));
				if (isMax)
					maxMin_eval = apply(maxMin_eval, _eval_root, MAX);
				else maxMin_eval = apply(maxMin_eval, _eval_root, MIN);
				
				maxMin_eval = reduceLinearize(maxMin_eval); 
				maxMin_eval = reduceLP(maxMin_eval); // Result should be canonical
				//_log.println("max of constrained root sub and int_eval(LB/UB): " + getString(max_eval));
			}

			// Finally, multiply in boolean decisions and irrelevant comparison expressions
			// to the XADD and add it to the running sum
			for (Map.Entry<Decision, Boolean> me : var_indep_decisions.entrySet()) {
				double high_val = me.getValue() ? 1d : 0d;
				double low_val = me.getValue() ? 0d : 1d;
				int V = getVarNode(me.getKey(), low_val, high_val);
				int notV = getVarNode(me.getKey(), high_val, low_val);
				V = makeCanonical(V);
				notV = makeCanonical(notV);
				DoubleExpr T = (DoubleExpr) (isMax ? NEG_INFINITE : POS_INFINITE);
				maxMin_eval = apply(apply(maxMin_eval, V, PROD), apply(getTermNode(T), notV, PROD), SUM);
				//maxMin_eval = apply(maxMin_eval, getVarNode(me.getKey(), low_val, high_val), PROD);
			}
			maxMin_eval = reduceLinearize(maxMin_eval); 
			//_log.println("After linearize, before reduceLP: " + getString(max_eval));
			maxMin_eval = reduceLP(maxMin_eval); // Result should be canonical
			//_log.println("After linearize and reduceLP: " + getString(max_eval));
			//_hsSpecialNodes.add(_runningMax);
			if (_runningMaxMin == -1) 
				_runningMaxMin = maxMin_eval;
			else 
			{
				if (isMax)
					_runningMaxMin = apply(_runningMaxMin, maxMin_eval, MAX);
				else _runningMaxMin = apply(_runningMaxMin, maxMin_eval, MIN);
			}
			//_runningMax = reduceLP(_runningMax);
			// _runningMax = apply(_runningMax, int_eval, MAX);
			// reduceLP
			//HashSet<String> all_vars = collectVars(_runningMax);
			//all_vars.removeAll(_hsBooleanVars);
			//_runningMax = reduceRound(_runningMax);
			_runningMaxMin = reduceLinearize(_runningMaxMin);
			_runningMaxMin = reduceLP(_runningMaxMin);
			//_hsSpecialNodes.add(_runningMax);
			_runningMaxMin = makeCanonical(_runningMaxMin);
			//if (_runningMax != makeCanonical(_runningMax)) {
			//	System.err.println("processXADDMax ERROR: encountered non-canonical node that should have been canonical");
			//	System.exit(1);
			//}
			//_log.println("running max result: " + getString(_runningMax));

			// All return information is stored in _runningMax so no need to return
			// any information here... just keep diagram as is
			return getTermNode(leaf_val);
		}


		
	
	}


////////////////////////////////////////////////////////////////////////////
	// Given argument var v, the XADD on which this is called contains
	// substitutions
	// for v at its leaves that are to be substituted into argument XADD xadd
	// and returned
	// at the leaves (because these branches are the conditions under which the
	// substitutions
	// are made).
	//
	// Need to ensure make_canonical is true in this case
	public class DeltaFunctionSubstitution extends XADDLeafOperation {
		String _subVar;
		int _xaddSubAtLeaves = -1;
		HashMap<String, ArithExpr> _leafSubs = new HashMap<String, ArithExpr>();

		public DeltaFunctionSubstitution(String subvar, int xadd_sub_at_leaves) {
			_subVar = subvar;
			_xaddSubAtLeaves = xadd_sub_at_leaves;
		}

		// TODO: revisit whether caching is possible, or in what circumstances
		public boolean isCacheable() {
			return false;
		}

		public int processXADDLeaf(ArrayList<Decision> decisions,
				ArrayList<Boolean> decision_values, ArithExpr leaf_val) {

			// Return an XADD for the resulting expression
			_leafSubs.clear();
			_leafSubs.put(_subVar, leaf_val);
			return substitute(_xaddSubAtLeaves, _leafSubs);
		}

		public int hashCode() {
			return _subVar.hashCode() + _xaddSubAtLeaves;
		}
	}

	public class XADDLeafDerivative extends XADDLeafOperation {
		String _derivativeVar;

		public XADDLeafDerivative(String deriv_var) {
			_derivativeVar = deriv_var.intern();
		}

		// TODO: verify this is cacheable... should be, just returns modified
		// subdiagrams
		public boolean isCacheable() {
			return true;
		}

		public int processXADDLeaf(ArrayList<Decision> decisions, ArrayList<Boolean> decision_values, ArithExpr leaf_val) {

			// Return an XADD for the resulting expression
			ArithExpr ret_expr = leaf_val.differentiateExpr(_derivativeVar);
			return getTermNode(ret_expr);
		}

	}

	public class XADDLeafIndefIntegral extends XADDLeafOperation {
		String _integrationVar;

		public XADDLeafIndefIntegral(String integration_var) {
			_integrationVar = integration_var.intern();
		}

		// TODO: revisit whether caching is possible... should be, just
		// returning integrated subdiagrams
		public boolean isCacheable() {
			return true;
		}

		public int processXADDLeaf(ArrayList<Decision> decisions, ArrayList<Boolean> decision_values, ArithExpr leaf_val) {

			// Return an XADD for the resulting expression
			ArithExpr ret_expr = leaf_val.integrateExpr(_integrationVar);
			return getTermNode(ret_expr);
		}

	}

	public int computeDefiniteIntegral(int xadd, String int_var) {
		XADDLeafDefIntegral integrator = new XADDLeafDefIntegral(int_var);
		reduceProcessXADDLeaf(xadd, integrator, /* canonical_reorder */false);
		return integrator._runningSum;
	}

	public class XADDLeafDefIntegral extends XADDLeafIndefIntegral {
		int _runningSum; // XADD for the running sum of all leaf substitutions
		double _integrationVarCoef;

		public final static boolean DEBUG_XADD_DEF_INTEGRAL = false;

		public XADDLeafDefIntegral(String integration_var) {
			super(integration_var);
			_integrationVarCoef = Double.NEGATIVE_INFINITY;

			// Start with the zero XADD
			_runningSum = getTermNode(ZERO);
		}

		// TODO: revisit whether caching is possible, or in what circumstances
		// (i.e., constraints
		// irrelevant to the integration variable)
		public boolean isCacheable() {
			return false;
		}

		public int processXADDLeaf(ArrayList<Decision> decisions,
				ArrayList<Boolean> decision_values, ArithExpr leaf_val) {

			// Multiply these in later
			HashMap<Decision, Boolean> int_var_indep_decisions = new HashMap<Decision, Boolean>();

			// upper and lower bounds based on the decisions
			if (DEBUG_XADD_DEF_INTEGRAL) {
				System.out.println("=============================");
				System.out.println("Current node: " + leaf_val);
				System.out.println("Decisions to get to get here: " + decisions
						+ " = " + decision_values + "\n===\n");
			}
			ArrayList<ArithExpr> lower_bound = new ArrayList<ArithExpr>();
			ArrayList<ArithExpr> upper_bound = new ArrayList<ArithExpr>();
			for (int i = 0; i < decisions.size(); i++) {
				Decision d = decisions.get(i);
				Boolean is_true = decision_values.get(i);
				CompExpr comp = null;
				if (d instanceof BoolDec) {
					int_var_indep_decisions.put(d, is_true);
					continue;
				} else if (d instanceof ExprDec) {
					ExprDec ed = (ExprDec) d;
					comp = ed._expr;
				} else {
					System.out
					.println("processXADDLeaf: Unsupported decision type '"
							+ d + "'");
					System.exit(1);
				}

				// Check that comparison expression is normalized
				if (!comp._rhs.equals(ZERO)) {
					System.out
					.println("processXADDLeaf: Expected RHS = 0 for '"	+ comp + "'");
					System.exit(1);
				}

				// Takes ArithExpr expr1 linear in var, returns (coef,expr2) where expr1 = coef*x + expr2
				CoefExprPair p = comp._lhs.removeVarFromExpr(_integrationVar); 
				ArithExpr lhs_isolated = p._expr;
				double    var_coef     = p._coef;
				if (DEBUG_XADD_DEF_INTEGRAL) {
					System.out.println("Pre: " + comp + " == " + is_true + ", int var [" + _integrationVar + "]"
							+ "\nLHS isolated: " + lhs_isolated + "\n ==>  " + var_coef + " * "
							+ _integrationVar);
				}

				if (var_coef == 0d) {
					int_var_indep_decisions.put(d, is_true);
					continue;
				}

				// We have coef*x + expr COMP_OPER 0
				boolean flip_comparison = (var_coef < 0d)&& (comp._type != EQ) && (comp._type != NEQ);
				ArithExpr new_rhs = (ArithExpr) new OperExpr(MINUS, ZERO,new OperExpr(PROD, new DoubleExpr(	1d / var_coef), lhs_isolated)).makeCanonical();

				// Divide through by coef (pos or neg)
				// - if coef neg, flip expression
				// - if decision neg, flip expression
				// - if both, don't flip
				int comp_oper = comp._type;
				if ((/* negated */!is_true && !flip_comparison)
						|| (/* not negated */is_true && flip_comparison)) {
					comp_oper = CompExpr.flipCompOper(comp_oper);
				}

				// Now we have x COMP_OPER expr
				// System.out.println("After arrange: " + new
				// CompExpr(comp_oper, new VarExpr(_integrationVar),
				// new_rhs));

				// Now mark this as a lower or upper bound
				// - lower bounds: x > f(y), x >= f(y)
				// - upper bounds: x < f(z), x <= f(z)
				if (comp_oper == GT || comp_oper == GT_EQ)
					lower_bound.add(new_rhs);
				else if (comp_oper == LT || comp_oper == LT_EQ)
					upper_bound.add(new_rhs);
				else {
					System.out.println("Cannot currently handle: "
							+ new CompExpr(comp_oper, new VarExpr(
									_integrationVar), new_rhs));
					System.out
					.println("Note: = triggers substitution, not sure how to handle ~=");
					new Exception().printStackTrace();
					System.exit(1);
				}
			}

			// Now explicitly compute lower and upper bounds as XADDs
			//
			// If these are polynomials, must go to +/- infinity at limits so
			// cannot
			// be used to approximate cdfs. Hence we must assume that there will
			// always
			// be limits on the polynomial functions implicit in the bounds.
			int xadd_lower_bound = -1;
			if (lower_bound.isEmpty()) {
				if (DEBUG_XADD_DEF_INTEGRAL) {
					System.err.println("No explicit lower bound given for '"
							+ _integrationVar + "', using -1e6");
					System.err.println("Constraints: " + decisions);
					System.err.println("Assignments: " + decision_values);
				}
				xadd_lower_bound = getTermNode(new DoubleExpr(-1e6));
			} else {
				if (DEBUG_XADD_DEF_INTEGRAL)
					System.out.println("Lower bounds: " + lower_bound);
				for (ArithExpr e : lower_bound) {
					if (xadd_lower_bound == -1) {
						xadd_lower_bound = getTermNode(e);
					} else {
						// Lower bound is max of all lower bounds
						xadd_lower_bound = apply(xadd_lower_bound,
								getTermNode(e), MAX);
					}
				}
			}

			int xadd_upper_bound = -1;
			if (upper_bound.isEmpty()) {
				if (DEBUG_XADD_DEF_INTEGRAL) {
					System.err.println("No explicit upper bound given for '"
							+ _integrationVar + "', using +1e6");
					System.err.println("Constraints: " + decisions);
					System.err.println("Assignments: " + decision_values);
				}
				xadd_upper_bound = getTermNode(new DoubleExpr(1e6));
			} else {
				if (DEBUG_XADD_DEF_INTEGRAL)
					System.out.println("Upper bounds: " + upper_bound);
				for (ArithExpr e : upper_bound) {
					if (xadd_upper_bound == -1) {
						xadd_upper_bound = getTermNode(e);
					} else {
						// Upper bound is min of all upper bounds
						xadd_upper_bound = apply(xadd_upper_bound,
								getTermNode(e), MIN);
					}
				}
			}

			// Build all constraints for the integration
			for (ArithExpr e1 : upper_bound) {
				for (ArithExpr e2 : lower_bound) {
					CompExpr ce = new CompExpr(GT, e1, e2);
					ExprDec ed = new ExprDec(ce);
					int_var_indep_decisions.put(ed, Boolean.TRUE);
				}
			}

			// Display lower and upper bounds
			if (DEBUG_XADD_DEF_INTEGRAL) {
				System.out.println("Lower bound:\n"	+ getString(xadd_lower_bound));
				System.out.println("Upper bound:\n"	+ getString(xadd_upper_bound));
			}

			// Compute the integral of this leaf w.r.t. the integration variable
			ArithExpr leaf_integral = leaf_val.integrateExpr(_integrationVar);
			if (DEBUG_XADD_DEF_INTEGRAL)
				System.out.println("Integral: " + leaf_integral);

			// Now compute:
			// leaf_integral{int_var = xadd_upper_bound} - leaf_integral{int_var
			// = xadd_lower_bound}
			int int_eval_lower = substituteXADDforVarInArithExpr(leaf_integral,	_integrationVar, xadd_lower_bound);
			int int_eval_upper = substituteXADDforVarInArithExpr(leaf_integral,	_integrationVar, xadd_upper_bound);
			int int_eval = apply(int_eval_upper, int_eval_lower, MINUS);
			// System.out.println("Result: " + getString(int_eval));

			// Finally, multiply in boolean decisions and irrelevant comparison
			// expressions
			// to the XADD and add it to the running sum
			//
			// - HashMap<Decision,Boolean> int_var_indep_decisions
			for (Map.Entry<Decision, Boolean> me : int_var_indep_decisions
					.entrySet()) {
				double high_val = me.getValue() ? 1d : 0d;
				double low_val = me.getValue() ? 0d : 1d;
				int_eval = apply(int_eval,getVarNode(me.getKey(), low_val, high_val), PROD);
			}
			_runningSum = apply(_runningSum, int_eval, SUM);

			// All return information is stored in _runningSum so no need to
			// return
			// any information here... just keep diagram as is
			// System.out.println("Running sum: " + getString(_runningSum));
			return getTermNode(leaf_val);
		}

		
	}

	// Note: use canonical_reorder=false for integration since internal nodes
	// *cannot* get
	// out of order, but use canonical_reorder=true for substitution
	public int reduceProcessXADDLeaf(int id, XADDLeafOperation leaf_sub,
			boolean canonical_reorder) {
		int ret_node = reduceProcessXADDLeaf(id, leaf_sub,
				new ArrayList<Decision>(), new ArrayList<Boolean>());
		if (canonical_reorder)
			return makeCanonical(ret_node);
		else
			return ret_node;
	}

	public IntPair _tempReduceLeafOpKey = new IntPair(-1, -1);

	private int reduceProcessXADDLeaf(int id, XADDLeafOperation leaf_op,
			ArrayList<Decision> decisions, ArrayList<Boolean> decision_values) {

		// System.out.println("** Reduce: decisions " + decisions + " -> " +
		// decision_values);

		Integer ret = null;
		XADDNode n = _hmInt2Node.get(id);
		if (n == null) {
			System.out.println("ERROR: " + id
					+ " expected in node cache, but not found!");
			new Exception().printStackTrace();
			System.exit(1);
		}

		// A terminal node should be reduced (and cannot be restricted)
		// by default if hashing and equality testing are working in getTNode
		if ((n instanceof XADDTNode) && (leaf_op instanceof XADDLeafMaxMin)) {
			return ((XADDLeafMaxMin) leaf_op).processXADDLeaf(decisions,
					decision_values, ((XADDTNode) n)._expr); // Assuming that to have
			// a node id means
			// canonical
		}
		if (n instanceof XADDTNode) {
			return leaf_op.processXADDLeaf(decisions, decision_values,
					((XADDTNode) n)._expr); // Assuming that to have
			// a node id means
			// canonical
		}

		// If its an internal node, check the reduce cache
		_tempReduceLeafOpKey.set(id, leaf_op.hashCode());
		if (leaf_op.isCacheable()
				&& (ret = _hmReduceLeafOpCache.get(_tempReduceLeafOpKey)) != null) {
			// System.out.println("** In cache, returning: " + getString(ret));
			return ret;
		}

		XADDINode inode = (XADDINode) n;
		Decision d = _alOrder.get(inode._var);

		decisions.add(d);
		decision_values.add(Boolean.FALSE);
		int low = reduceProcessXADDLeaf(inode._low, leaf_op, decisions,
				decision_values);

		decision_values.set(decision_values.size() - 1, Boolean.TRUE);
		int high = reduceProcessXADDLeaf(inode._high, leaf_op, decisions,
				decision_values);

		decisions.remove(decisions.size() - 1);
		decision_values.remove(decision_values.size() - 1);

		// Standard Reduce: getInode will handle the case of low == high
		ret = getINode(inode._var, low, high);

		// Put return value in cache and return
		_hmReduceLeafOpCache.put(new IntPair(id, leaf_op.hashCode()), ret);
		return ret;
	}


///////////////////////////////////////////////////////////////////////////////
//                           Helper Internal Classes
///////////////////////////////////////////////////////////////////////////////

	public static class CoefExprPair {
		public ArithExpr _expr;
		public double    _coef;
		public CoefExprPair(ArithExpr expr, double coef) {
			_expr = expr;
			_coef = coef;
		}
	}
	
	public abstract class XADDNode {
		public int _mark;

		public void mark() {
			_mark = _markCounter;
		}

		public void unmark() {
			_mark = 0;
		}

		public boolean isMarked() {
			return _mark == _markCounter;
		}

		public String toString() {
			return toString(0);
		}

		public HashSet<XADDNode> collectNodes() {
			HashSet<XADDNode> nodes = new HashSet<XADDNode>();
			collectNodes(nodes);
			return nodes;
		}

		public HashSet<String> collectVars() {
			HashSet<String> vars = new HashSet<String>();
			collectVars(vars);
			return vars;
		}

		public abstract int countBranches();

		public abstract String toString(int depth);

		public abstract String toString(boolean format);

		public abstract void toGraph(Graph g, int id);

		public abstract void collectVars(HashSet<String> vars);

		public abstract void collectNodes(HashSet<XADDNode> nodes);
	}

	public class XADDTNode extends XADDNode {
		public ArithExpr _expr;
		public Object    _annotate;
		
		public XADDTNode(ArithExpr e) {
			if (e instanceof OperExpr && ((OperExpr) e)._terms.size() == 1)
				_expr = ((OperExpr) e)._terms.get(0);
			else
				_expr = e;
			_annotate = null;
		}

		public void set(ArithExpr e, Object annotation) {
			_expr = e;
			_annotate = annotation;
		}

		public XADDTNode(ArithExpr e, Object annotation) {
			if (e instanceof OperExpr && ((OperExpr) e)._terms.size() == 1)
				_expr = ((OperExpr) e)._terms.get(0);
			else
				_expr = e;
			_annotate = annotation;
		}

		public int hashCode() {
			if (_annotate == null) 
				return _expr.hashCode();
			else
				return _expr.hashCode() + _annotate.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof XADDTNode) {
				XADDTNode t = (XADDTNode)o;
				if (_annotate == null)
					return t._annotate == null && t._expr.equals(_expr);
				else 
					return t._annotate.equals(_annotate) && t._expr.equals(_expr);
			} else 
				return false;
		}

		public void collectVars(HashSet<String> vars) {
			_expr.collectVars(vars);
		}

		public void collectNodes(HashSet<XADDNode> nodes) {
			nodes.add(this);
		}

		public void toGraph(Graph g, int id) {
			String this_node = Integer.toString(id);
			g.addNode(this_node);
			if (_annotate == null)
				g.addNodeLabel(this_node, _expr.toString());
			else
				g.addNodeLabel(this_node, _expr.toString() + "\n[ " + _annotate + " ]");

			if (GRAPH_USE_COLOR)
				g.addNodeColor(this_node, "lightsalmon"); // red, darkred, lightsalmon
			g.addNodeShape(this_node, "box");
			g.addNodeStyle(this_node, "filled");
		}

		public String toString(int depth) {
			return "( ["/* "#" + _hmNode2Int.get(this) + ": " */
					+ _expr.toString() + "] )";
		}

		public String toString(boolean format) {
			return "( ["/* "#" + _hmNode2Int.get(this) + ": " */
					+ _expr.toString(format) + "] )";
		}

		@Override
		public int countBranches() {
			return 1;
		}

	}

	public class XADDINode extends XADDNode {
		public int _var;
		public int _low;
		public int _high;

		public XADDINode(int var, int low, int high) {
			_var = var;
			_low = low;
			_high = high;
		}

		public void set(int var, int low, int high) {
			_var = var;
			_low = low;
			_high = high;
		}

		public int hashCode() {
			return (_var) + (_low << 10) - (_high << 20) + (_high >>> 20)
					- (_low >>> 10);
		}

		public boolean equals(Object o) {
			if (o instanceof XADDINode) {
				XADDINode n = (XADDINode) o;
				return this._var == n._var && this._low == n._low
						&& this._high == n._high;
			} else
				return false;
		}

		public void collectNodes(HashSet<XADDNode> nodes) {
			if (nodes.contains(this))
				return;

			nodes.add(this);
			_hmInt2Node.get(_low).collectNodes(nodes);
			_hmInt2Node.get(_high).collectNodes(nodes);
		}

		public void collectVars(HashSet<String> vars) {

			// Check cache
			HashSet<String> vars2 = _hmINode2Vars.get(this);
			if (vars2 != null) {
				vars.addAll(vars2);
				return;
			}

			XADDNode low = _hmInt2Node.get(_low);
			XADDNode high = _hmInt2Node.get(_high);
			Decision d = _alOrder.get(_var);
			d.collectVars(vars);
			low.collectVars(vars);
			high.collectVars(vars);

			_hmINode2Vars.put(this, (HashSet<String>) vars.clone());
		}

		public void toGraph(Graph g, int id) {

			// Main node
			String this_node = Integer.toString(id);
			// System.out.println("var: " + _var);
			// System.out.println(_alOrder);
			g.addNode(this_node);
			g.addNodeLabel(this_node, _alOrder.get(_var).toString()/*
			 * +" id: "+
			 * getVarIndex
			 * (
			 * _alOrder.
			 * get
			 * (_var),
			 * true)
			 */);
			if (GRAPH_USE_COLOR)
				g.addNodeColor(this_node, "lightblue"); // green, lightblue
			g.addNodeShape(this_node, "ellipse");
			g.addNodeStyle(this_node, "filled");

			// Children
			XADDNode low = _hmInt2Node.get(_low);
			if (low != null) {
				String low_node = Integer.toString(_low);
				g.addUniLink(this_node, low_node, "black", "dashed",
						Graph.EMPTY_STR);
				low.toGraph(g, _low);
			}

			XADDNode high = _hmInt2Node.get(_high);
			if (high != null) {
				String high_node = Integer.toString(_high);
				g.addUniLink(this_node, high_node, "black", "solid",
						Graph.EMPTY_STR);
				high.toGraph(g, _high);
			}
		}

		public String toString(int depth) {
			return toString(depth, true);
		}

		public String toString(int depth, boolean format) {
			StringBuffer sb = new StringBuffer();
			sb.append("( "/*
			 * "#" + _hmNode2Int.get(this) + " v" + _var + ": "
			 */+ "[" + _alOrder.get(_var).toString(format) + "]");

			// Node level cache
			XADDNode n2 = _hmInt2Node.get(_high);
			if (n2 != null) {
				sb.append("\n" + indent(depth) + " " + n2.toString(depth + 1)
						+ " ");
			} else {
				sb.append("h:[null] ");
			}
			XADDNode n1 = _hmInt2Node.get(_low);
			if (n1 != null) {
				sb.append("\n" + indent(depth) + " " + n1.toString(depth + 1)
						+ " ");
			} else {
				sb.append("l:[null] ");
			}
			sb.append(") ");

			return sb.toString();
		}

		@Override
		public int countBranches() {
			int low_count = _hmInt2Node.get(_low).countBranches();
			if (low_count > MAX_BRANCH_COUNT || low_count == -1)
				return -1;

			int high_count = _hmInt2Node.get(_high).countBranches();
			if (high_count > MAX_BRANCH_COUNT || high_count == -1)
				return -1;

			int total = low_count + high_count;
			if (total > MAX_BRANCH_COUNT)
				return -1;

			return total;
		}

		@Override
		public String toString(boolean format) {
			return toString(0, format);
		}
	}

	// //////////////////////////////////////////////////////////////

	public abstract class Decision implements Serializable{
		public abstract void collectVars(HashSet<String> vars);

	public Decision divideRound(ExprDec e) 
	{
		
		// For decision node also makeCanonical by dividing coeff of first variable by rest of the variables
		ArithExpr new_lhs = ArithExpr.op(e._expr._lhs, e._expr._rhs,MINUS);
		new_lhs = (ArithExpr) new_lhs.makeCanonical();
		CompExpr current_expr = new CompExpr(e._expr._type, new_lhs, ZERO);
		String contVar = null;
		for (int i = 0; i < _alContinuousVars.size(); i++) {
					contVar = _alContinuousVars.get(i);
					DoubleExpr doubleCoef = (DoubleExpr) ZERO;
					// first look for x*x
					if (HANDLE_NONLINEAR)
						doubleCoef = findVar(current_expr._lhs, contVar,true);
					if (doubleCoef == (DoubleExpr) ZERO)
						doubleCoef = findVar(current_expr._lhs, contVar,false);
					if (doubleCoef != (DoubleExpr) ZERO) 
					{
						boolean flip_comparison = false;
						flip_comparison = (doubleCoef._dConstVal < 0d)&& (current_expr._type != EQ)&& (current_expr._type != NEQ);

						current_expr._lhs = (ArithExpr) (new OperExpr(PROD,	(ArithExpr.op(new DoubleExpr(1d),doubleCoef, DIV)),
										current_expr._lhs)).makeCanonical();
						int comp_oper = current_expr._type;
						if (flip_comparison)
							switch (comp_oper) 
							{
							case GT:
								current_expr._type = LT;
								break;
							case GT_EQ:
								current_expr._type = LT_EQ;
								break;
							case LT:
								current_expr._type = GT;
								break;
							case LT_EQ:
								current_expr._type = GT_EQ;
								break;
							}

						// ((ExprDec) d)._expr = comp;
						break;
					}
				}
				e._expr = current_expr;
				OperExpr lhs = (OperExpr) e._expr._lhs;
				for (ArithExpr a : lhs._terms)
				{

					if (a instanceof OperExpr && ((OperExpr) a)._type == PROD) 
					{

						for (ArithExpr a1 : ((OperExpr) a)._terms) 
							if (a1 instanceof DoubleExpr)
								((DoubleExpr)a1)._dConstVal = Math.round(((DoubleExpr)a1)._dConstVal*1000d)/1000d ; 

					} 
					else if (a instanceof DoubleExpr) 
						((DoubleExpr)a)._dConstVal = Math.round(((DoubleExpr)a)._dConstVal*1000d)/1000d ; 

				}
			
			return e;
		}

		public abstract String toString(boolean format);

		public abstract Decision makeCanonical();
		
		
	}

	public class NullDec extends Decision implements Serializable{

		public void collectVars(HashSet<String> vars) {
		}

		public Decision makeCanonical() {
			return this;
		}

		public String toString(boolean format) {
			return "[NULL DECISION]";
		}

		public int hashCode() {
			return 0;
		}

		public boolean equals(Object o) {
			return (o instanceof NullDec);
		}

	}

	// Represents a tautology or its negation (inconsistency)
	public class TautDec extends Decision implements Serializable{
		public boolean _bTautology;

		public TautDec(boolean isTaut) {
			_bTautology = isTaut;
		}

		public int hashCode() {
			return _bTautology ? 1 : 0;
		}

		public boolean equals(Object o) {
			if (o instanceof TautDec)
				return ((TautDec) o)._bTautology == _bTautology;
			else
				return false;
		}

		public void collectVars(HashSet<String> vars) {
		}

		public String toString() {
			return Boolean.toString(_bTautology);
		}

		public Decision makeCanonical() {
			return this;
		}

		@Override
		public String toString(boolean format) {
			return Boolean.toString(_bTautology);
		}
	}

	public class BoolDec extends Decision implements Serializable{
		public String _sVarName = null;

		public BoolDec(String var_name) {
			_sVarName = var_name.intern();
			_alBooleanVars.add(_sVarName);
			_hsBooleanVars.add(_sVarName);
		}

		public int hashCode() {
			return _sVarName.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof BoolDec)
				return ((BoolDec) o)._sVarName == _sVarName;
			else
				return false;
		}

		public void collectVars(HashSet<String> vars) {
			vars.add(_sVarName);
		}

		public String toString() {
			return _sVarName;
		}

		public Decision makeCanonical() {
			return this;
		}

		@Override
		public String toString(boolean format) {
			return toString();
		}
	}

	public class ExprDec extends Decision implements Serializable{
		public CompExpr _expr = null;

		public ExprDec(CompExpr expr) {
			_expr = expr;
		}

		public int hashCode() {
			return _expr.hashCode();
		}

		public boolean equals(Object o) {
			if (o instanceof ExprDec)
				return ((ExprDec) o)._expr.equals(_expr);
			else
				return false;
		}

		public ExprDec clone()
		{
			
			CompExpr new_expr = null;
			//new_expr = SerialClone.clone(this._expr);
			new_expr = this._expr.clone();
			return new ExprDec(new_expr);
		}
		
		public void collectVars(HashSet<String> vars) {
			_expr._lhs.collectVars(vars);
			_expr._rhs.collectVars(vars);
		}

		public String toString() {
			return _expr.toString();
		}

		public String toString(boolean format) {
			return _expr.toString(format);
		}

		public Decision makeCanonical() {

			// Make canonical
			Decision d = this;
			if (d instanceof ExprDec) {
				ExprDec e = (ExprDec) d;
				// have to add the decisions from the divisor node to the
				// decisions
				// if the decision of the divisor is positive, the decision d's
				// sign does not change, else flip the decision type.
				CompExpr new_comp = (CompExpr) e._expr.makeCanonical();
				d = new ExprDec(new_comp);
				// if there were divisors, add the decisions based on the
				// expressions

			}

			// Check for tautology (or inconsistency)
			if (d instanceof ExprDec
					&& ((ExprDec) d)._expr._lhs instanceof DoubleExpr
					&& ((ExprDec) d)._expr._rhs instanceof DoubleExpr) {
				// Directly evaluate the inequality
				double dval_lhs = ((DoubleExpr) ((ExprDec) d)._expr._lhs)._dConstVal;
				double dval_rhs = ((DoubleExpr) ((ExprDec) d)._expr._rhs)._dConstVal;
				TautDec tdec = null;
				switch (((ExprDec) d)._expr._type) {
				case EQ:
					tdec = new TautDec(dval_lhs == dval_rhs);
					break;
				case NEQ:
					tdec = new TautDec(dval_lhs != dval_rhs);
					break;
				case GT:
					tdec = new TautDec(dval_lhs > dval_rhs);
					break;
				case GT_EQ:
					tdec = new TautDec(dval_lhs >= dval_rhs);
					break;
				case LT:
					tdec = new TautDec(dval_lhs < dval_rhs);
					break;
				case LT_EQ:
					tdec = new TautDec(dval_lhs <= dval_rhs);
					break;
				}
				if (tdec != null)
					d = tdec;
			} else if (d instanceof ExprDec && CHECK_MIN_MAX) {
				// Check for evaluations based on minimum and maximum values
				// ExprDec d1 = (ExprDec)d;
				TautDec tdec = checkRangeImpliedDecision((ExprDec) d);
				if (tdec != null) {
					d = tdec;
				}
			}

			return d;
		}

	}

	public static DoubleExpr findVar(ArithExpr expr, String action,
			boolean nonlinear) {
		DoubleExpr result = (DoubleExpr) ZERO;
		if (expr instanceof OperExpr && ((OperExpr) expr)._type == SUM) {
			// sum of products
			OperExpr eOp = ((OperExpr) expr);
			for (ArithExpr e : eOp._terms) {
				if (e instanceof OperExpr) {
					result = findVarTerm((OperExpr) e, action, nonlinear);
					if (result != (DoubleExpr) ZERO)
						return result;
				} else if (e instanceof VarExpr) {
					OperExpr temp = new OperExpr(PROD, Arrays.asList(e));
					result = findVarTerm(temp, action, nonlinear);
					if (result != (DoubleExpr) ZERO)
						return result;
				}
			}
		} else if (expr instanceof OperExpr && ((OperExpr) expr)._type == PROD) {
			result = findVarTerm((OperExpr) expr, action, nonlinear);
			if (result != (DoubleExpr) ZERO)
				return result;
		} else if ((expr instanceof VarExpr) || (expr instanceof DoubleExpr)) {
			OperExpr temp = new OperExpr(PROD, Arrays.asList(expr));
			result = findVarTerm(temp, action, nonlinear);
			if (result != (DoubleExpr) ZERO)
				return result;
		}
		return result;
	}

	// A single term (PROD)

	public static DoubleExpr findVarTerm(OperExpr expr, String action1,
			boolean nonlinear) {
		DoubleExpr result = (DoubleExpr) ZERO;

		// Process all terms (optional double followed by vars)
		int _var_count = 0;
		double coef = 1d;
		for (ArithExpr e : expr._terms) {
			if (e instanceof DoubleExpr) {
				coef *= ((DoubleExpr) e)._dConstVal;
			} else if (e instanceof OperExpr) {
				// don't divide if it comes here, makes it complicated
			} else if (e instanceof VarExpr) {
				// Both interned so we can test direct equality
				if (((VarExpr) e)._sVarName.equals(action1)) {
					_var_count++;
				}
			} else {
				System.out.println("findVarTerm: Unsupported expression '" + e
						+ "'");
				System.exit(1);
			}
		}

		if ((nonlinear) && (_var_count > 1))
			return new DoubleExpr(coef);
		else if ((!nonlinear) && (_var_count > 0))
			return new DoubleExpr(coef);
		else
			return (DoubleExpr) ZERO;

	}

	public TautDec checkRangeImpliedDecision(ExprDec d) {
		TautDec tdec = null;
		Double lhs_max = d._expr._lhs.evaluateRange(_hmMinVal, _hmMaxVal, false);
		Double lhs_min = d._expr._lhs.evaluateRange(_hmMinVal, _hmMaxVal, true);
		Double rhs_max = d._expr._rhs.evaluateRange(_hmMinVal, _hmMaxVal, false);
		Double rhs_min = d._expr._rhs.evaluateRange(_hmMinVal, _hmMaxVal, true);
		if (lhs_max == null)
			lhs_max = Double.MAX_VALUE;
		if (rhs_max == null)
			rhs_max = Double.MAX_VALUE;
		if (lhs_min == null)
			lhs_min = -Double.MAX_VALUE;
		if (rhs_min == null)
			rhs_min = -Double.MAX_VALUE;
		switch (d._expr._type) {
		case EQ:
		case NEQ:
			if ((lhs_min > rhs_max || rhs_min > lhs_max)
					|| ((lhs_max == lhs_min) && (rhs_max == rhs_min) && (lhs_min != rhs_min))) {
				// Indicates they cannot possibly be equal
				tdec = new TautDec((d._expr._type == EQ) ? false : true);
			}
			break;
		case GT:
			// lhs > rhs
			if (lhs_min > rhs_max)
				tdec = new TautDec(true);
			else if (lhs_max <= rhs_min)
				tdec = new TautDec(false);
			break;
		case GT_EQ:
			// lhs >= rhs
			if (lhs_min >= rhs_max)
				tdec = new TautDec(true);
			else if (lhs_max < rhs_min)
				tdec = new TautDec(false);
			break;
		case LT:
			// lhs < rhs
			if (lhs_max < rhs_min)
				tdec = new TautDec(true);
			else if (lhs_min >= rhs_max)
				tdec = new TautDec(false);
			break;
		case LT_EQ:
			// lhs <= rhs
			if (lhs_max <= rhs_min)
				tdec = new TautDec(true);
			else if (lhs_min > rhs_max)
				tdec = new TautDec(false);
			break;
		}
		if (tdec != null) {
			//System.out.println("*** " + (tdec == null ? "not" : "")					+ " pruning " + d + " with " + tdec + " because...");
			//System.out.println("- [" + lhs_min + "," + lhs_max + "] "+ _aOpNames[d._expr._type] + " [" + rhs_min + "," + rhs_max+ "]");
		}

		return tdec;
	}

	// ///////////////////////////////////////////////////////////////////

	public static abstract class Expr implements Comparable<Expr>,Serializable {

		public static final Class DOUBLE_CLASS = DoubleExpr.class;
		public static final Class VAR_CLASS = VarExpr.class;
		public static final Class ARITH_CLASS = ArithExpr.class;
		public static final Class OPER_CLASS = OperExpr.class;
		public static final Class COMP_CLASS = CompExpr.class;

		public static HashMap<Class, Integer> _class2order = new HashMap<Class, Integer>();
		static {
			_class2order.put(DOUBLE_CLASS, 0);
			_class2order.put(VAR_CLASS, 1);
			_class2order.put(ARITH_CLASS, 2);
			_class2order.put(OPER_CLASS, 3);
			_class2order.put(COMP_CLASS, 4);
		}

		public abstract Expr makeCanonical();

		public int compareTo(Expr o) {
			// Var, Double, Arith, Oper, Comp
			Class this_class = this.getClass();
			Class other_class = o.getClass();

			if (!this_class.equals(other_class)) {
				Integer rank_this = _class2order.get(this_class);
				Integer rank_other = _class2order.get(other_class);
				return rank_this - rank_other;
			} else
				return this.hashCode() - o.hashCode();
		}
	}

	public static class CompExpr extends Expr implements Serializable{

		public int _type = UND;
		public ArithExpr _lhs = null;
		public ArithExpr _rhs = null;

		public CompExpr(int type, ArithExpr lhs, ArithExpr rhs) {
			_type = type;
			_lhs = lhs;
			_rhs = rhs;
		}

		public CompExpr clone()
		{
			ArithExpr lhs = (ArithExpr) this._lhs.clone();
			ArithExpr rhs = (ArithExpr) this._rhs.clone();
			CompExpr cmp =  new CompExpr(UND, lhs, rhs);
			cmp._type = new Integer(this._type);
			//cmp._lhs = SerialClone.clone(this._lhs);
			//cmp._rhs = SerialClone.clone(this._rhs);
			return cmp;
		}
		
		public String toString(boolean format) {
			return _lhs.toString(format) + " " + _aOpNames[_type] + " "
					+ _rhs.toString(format);
		}

		public static int flipCompOper(int comp_oper) {
			switch (comp_oper) {
			case GT:
				return LT_EQ;
			case GT_EQ:
				//return LT;
				return LT_EQ;
			case LT:
				return GT_EQ;
			case LT_EQ:
				//return GT;
				return GT_EQ;
			case EQ:
				return NEQ;
			case NEQ:
				return EQ;
			default:
				return -1;
			}
		}

		public Expr makeCanonical() {

			// 1. Expressions all zero on RHS of comparisons and restrict
			// symbols:
			// a > b : a <= b and swap branches
			// a < b : a >= b and swap branches
			// a != b : a == b and swap branches
			// CANONICAL_DIVISOR.clear();
			CompExpr new_expr = new CompExpr(_type, _lhs, _rhs);
			switch (new_expr._type) {
			case GT:
				new_expr._type = LT_EQ;
				// Swap lhs and rhs
				new_expr._lhs = _rhs;
				new_expr._rhs = _lhs;
				break;
			case LT:
				new_expr._type = GT_EQ;
				// Swap lhs and rhs
				new_expr._lhs = _rhs;
				new_expr._rhs = _lhs;
				break;
			case NEQ:
				new_expr._type = EQ;
				// Swap lhs and rhs
				new_expr._lhs = _rhs;
				new_expr._rhs = _lhs;
				break;
			}

		/*	ArithExpr new_lhs = ArithExpr.op(new_expr._lhs, new_expr._rhs, MINUS);
			new_lhs = (ArithExpr) new_lhs.makeCanonical();
			new_expr = new CompExpr(new_expr._type, new_lhs, ZERO);
			return new_expr;*/
			ArithExpr new_lhs = ArithExpr.op(new_expr._lhs, new_expr._rhs,
					MINUS);
			new_lhs = (ArithExpr) new_lhs.makeCanonical();
			CompExpr current_expr = new CompExpr(new_expr._type, new_lhs, ZERO);
			String contVar = null;
			boolean handlePrime = false;
			if (!(_alContinuousVars.isEmpty())) {
				for (int i = 0; i < _alContinuousVars.size(); i++) {
					contVar = _alContinuousVars.get(i);
					DoubleExpr doubleCoef = findVar(current_expr._lhs, contVar
							+ "'", false);
					if (doubleCoef != (DoubleExpr) ZERO) {
						handlePrime = true;
						break;
					}
				}
				// making sure that the primes are not considered
				if (!handlePrime) {
					for (int i = 0; i < _alContinuousVars.size(); i++) {
						contVar = _alContinuousVars.get(i);
						DoubleExpr doubleCoef = (DoubleExpr) ZERO;
						// first look for x*x
						if (HANDLE_NONLINEAR)
							doubleCoef = findVar(current_expr._lhs, contVar,
									true);
						if (doubleCoef == (DoubleExpr) ZERO)
							doubleCoef = findVar(current_expr._lhs, contVar,
									false);
						if (doubleCoef != (DoubleExpr) ZERO) {
							boolean flip_comparison = false;
							flip_comparison = (doubleCoef._dConstVal < 0d)
									&& (current_expr._type != EQ)
									&& (current_expr._type != NEQ);
							
							current_expr._lhs = (ArithExpr) (new OperExpr(PROD,
									(ArithExpr.op(new DoubleExpr(1d),
											doubleCoef, DIV)),
											current_expr._lhs)).makeCanonical();
							int comp_oper = current_expr._type;
							if (flip_comparison)
								switch (comp_oper) {
								case GT:
									current_expr._type = LT;
									break;
								case GT_EQ:
									current_expr._type = LT_EQ;
									break;
								case LT:
									current_expr._type = GT;
									break;
								case LT_EQ:
									current_expr._type = GT_EQ;
									break;
								}

							// ((ExprDec) d)._expr = comp;
							break;
						}
					}
				}
			}
			return current_expr;
		}

		private OperExpr removeDivisor(OperExpr expr, ArithExpr div) {
			// removing the divisor term from an OperExr that occurs on the
			// lhs/rhs
			// operands can be operExr or DoubleExpr
			ArrayList<ArithExpr> local_terms = new ArrayList<ArithExpr>(
					expr._terms);
			local_terms.set(1, new DoubleExpr(1d));
			// expr._type = PROD;
			// expr = (OperExpr) expr._terms.get(0);
			return new OperExpr(expr._type, local_terms);
			// removing the divisor term from the expression

		}

		// steps to multiply all terms by the divisor
		private ArithExpr checkDivisor(OperExpr changing_expr, ArithExpr divisor) {
			if (divisor == null) {
				if (changing_expr._type == DIV) {
					divisor = (ArithExpr) changing_expr._terms.get(1);
					// (1)remove the divisor term from that term
					changing_expr = removeDivisor(changing_expr, divisor);
					// do not take division sign out for the next iteration
					return divisor;

				}

				else // have to go inside the expr
				{
					for (int i = 0; i < changing_expr._terms.size(); i++) {
						if (changing_expr._terms.get(i) instanceof OperExpr)
							divisor = checkDivisor(
									(OperExpr) changing_expr._terms.get(i),
									divisor);
						if (divisor != null)
							break;
					}
				}
			}
			return divisor;
		}

		public OperExpr removeDivFromOtherTerms(OperExpr changing_expr,
				ArithExpr divisor) {
			OperExpr temp_expr = new OperExpr(changing_expr._type,
					changing_expr._terms);
			if (temp_expr._type == SUM)// we have to go in one level
			{
				ArrayList<ArithExpr> oper_list = new ArrayList<ArithExpr>();
				for (int i = 0; i < temp_expr._terms.size(); i++)
					if (temp_expr._terms.get(i) instanceof OperExpr)
						oper_list.add(removeDivFromOtherTerms(
								(OperExpr) temp_expr._terms.get(i), divisor));
					else if (temp_expr._terms.get(i) instanceof DoubleExpr)
						oper_list.add(ArithExpr.op(temp_expr._terms.get(i),
								divisor, PROD));
				for (int i = 0; i < oper_list.size(); i++)
					return new OperExpr(SUM, oper_list);
			}
			// found the first instance of divisor.search the rest of the expr
			// for the divisor
			// for (int j=0;j<changing_expr._terms.size();j++)
			// in the other statements there is either product or division (sum
			// of products, this level is the products level)
			else {
				if (temp_expr._type == DIV) {
					ArithExpr other_divisor = (ArithExpr) temp_expr._terms
							.get(1);
					// (1)remove the divisor term from that term
					if (divisor.equals(other_divisor)) {
						temp_expr = removeDivisor(temp_expr, divisor);
						temp_expr._type = PROD;
					} else
						temp_expr = (OperExpr) ArithExpr.op(temp_expr, divisor,
								PROD);
				} else if (temp_expr._type == PROD) {
					boolean removedDiv = false;
					for (int k = 0; k < temp_expr._terms.size(); k++)
						if (temp_expr._terms.get(k) instanceof OperExpr) {
							if ((((OperExpr) temp_expr._terms.get(k))._type == DIV)
									&& (((OperExpr) temp_expr._terms.get(k))._terms
											.get(1).equals(divisor))) {
								temp_expr._terms.set(
										k,
										removeDivisor(
												(OperExpr) temp_expr._terms
												.get(k), divisor));
								((OperExpr) temp_expr._terms.get(k))._type = PROD;
								removedDiv = true;
							} else if ((((OperExpr) temp_expr._terms.get(k))._type == DIV)
									&& (((OperExpr) temp_expr._terms.get(k))._terms
											.get(1).equals(1d)))// previously
								// found divisor
							{
								((OperExpr) temp_expr._terms.get(k))._type = PROD;
								removedDiv = true;
							}

						}// after if
					if (!removedDiv)
						temp_expr = (OperExpr) (ArithExpr.op(temp_expr,
								divisor, PROD));
				} else
					temp_expr = (OperExpr) (ArithExpr.op(temp_expr, divisor,
							PROD));
				// }
				// changing_expr.makeCanonical();
			}
			return new OperExpr(temp_expr._type, temp_expr._terms);
		}

		public boolean equals(Object o) {
			if (o instanceof CompExpr) {
				CompExpr c = (CompExpr) o;
				return this._type == c._type && this._lhs.equals(c._lhs)
						&& this._rhs.equals(c._rhs);
			} else
				return false;
		}

		public int hashCode() {
			int i2 = _lhs.hashCode();
			int i3 = _rhs.hashCode();
			return (_type) + (i2 << 10) - (i3 << 20) + (i3 >>> 20)
					- (i2 >>> 10);
		}

		public static CompExpr parse(String s) {
			try {
				FOPC.Node res = FOPC.parse(s);
				return Convert2CompExpr((FOPC.PNode) res);
			} catch (Exception f) {
				return null;
			}
		}

		public static CompExpr Convert2CompExpr(FOPC.PNode res) {
			int type = UND;
			if (res._nPredID != FOPC.PNode.INVALID) {
				switch (res._nPredID) {
				case FOPC.PNode.EQUALS: {
					type = res._bIsNegated ? NEQ : EQ;
				}
				break;
				case FOPC.PNode.LESS: {
					type = res._bIsNegated ? GT_EQ : LT;
				}
				break;
				case FOPC.PNode.LESSEQ: {
					type = res._bIsNegated ? GT : LT_EQ;
				}
				break;
				}
			}
			ArithExpr lhs = ArithExpr.Convert2ArithExpr((FOPC.Term) res
					.getBinding(0));
			ArithExpr rhs = ArithExpr.Convert2ArithExpr((FOPC.Term) res
					.getBinding(1));
			if (lhs == null || rhs == null || type == UND)
				return null;
			else
				return new CompExpr(type, lhs, rhs);
		}

		public String toString() {
			return _lhs + " " + _aOpNames[_type] + " " + _rhs;
		}

		public CompExpr substitute(HashMap<String, ArithExpr> subst) {
			ArithExpr lhs = _lhs.substitute(subst);
			ArithExpr rhs = _rhs.substitute(subst);
			return new CompExpr(_type, lhs, rhs);
		}

		public Boolean evaluate(HashMap<String, Double> cont_assign) {

			Double dval_lhs = _lhs.evaluate(cont_assign);
			Double dval_rhs = _rhs.evaluate(cont_assign);

			if (dval_lhs == null || dval_rhs == null)
				return null;

			switch (_type) {
			case EQ:
				return (dval_lhs == dval_rhs);
			case NEQ:
				return (dval_lhs != dval_rhs);
			case GT:
				return (dval_lhs > dval_rhs);
			case GT_EQ:
				return (dval_lhs >= dval_rhs);
			case LT:
				return (dval_lhs < dval_rhs);
			case LT_EQ:
				return (dval_lhs <= dval_rhs);
			default:
				return null;
			}
		}

		public void collectVars(HashSet<String> vars) {
			_lhs.collectVars(vars);
			_rhs.collectVars(vars);
		}
	}

	public abstract static class ArithExpr extends Expr implements Serializable{

		@Override
		protected Object clone() {
			// TODO Auto-generated method stub
			return null;
		}

		public static ArithExpr parse(String s) {
			try {
				FOPC.Node res = FOPC.parse(s + " = 0");
				// if (res != null)
				// System.out.println("==> " + res.toFOLString());
				return Convert2ArithExpr(((FOPC.PNode) res).getBinding(0));
			} catch (Exception e) {
				return null;
			}
		}

		public static int parseIntoXADD(XADD context, String s) {
			try {
				FOPC.Node res = FOPC.parse(s + " = 0");
				// if (res != null)
				// System.out.println("==> " + res.toFOLString());
				return Convert2XADD(context, ((FOPC.PNode) res).getBinding(0));
			} catch (Exception e) {
				System.err.println("Could not convert: " + s + "\n" + e);
				e.printStackTrace(System.err);
				System.exit(1);
				return -1;
			}
		}

		public abstract String toString(boolean format);

		public static ArithExpr Convert2ArithExpr(FOPC.Term t) {
			// System.out.println("Convert2ArithExpr: " + t.toFOLString());
			if (t instanceof FOPC.TVar) {
				return new VarExpr(((FOPC.TVar) t)._sName);
			} else if (t instanceof FOPC.TScalar) {
				return new DoubleExpr(((FOPC.TScalar) t)._dVal);
			} else if (t instanceof FOPC.TInteger) {
				return new DoubleExpr(((FOPC.TInteger) t)._nVal);
			} else if (t instanceof FOPC.TFunction) {
				return OperExpr.Convert2OperExpr((FOPC.TFunction) t);
			} else
				return null;
		}

		public static int Convert2XADD(XADD context, FOPC.Term t) {
			// System.out.println("Convert2ArithExpr: " + t.toFOLString());
			if (t instanceof FOPC.TVar) {
				return context.getTermNode(new VarExpr(((FOPC.TVar) t)._sName));
			} else if (t instanceof FOPC.TScalar) {
				return context.getTermNode(new DoubleExpr(
						((FOPC.TScalar) t)._dVal));
			} else if (t instanceof FOPC.TInteger) {
				return context.getTermNode(new DoubleExpr(
						((FOPC.TInteger) t)._nVal));
			} else if (t instanceof FOPC.TFunction) {
				return OperExpr.Convert2XADD(context, (FOPC.TFunction) t);
			} else
				return -1;
		}

		public static ArithExpr op(ArithExpr f1, ArithExpr f2, int op) {
			if (f1 instanceof DoubleExpr && (op == SUM || op == PROD)) {
				// operands reordered
				return op(f2, ((DoubleExpr) f1)._dConstVal, op);
			} else if (f2 instanceof DoubleExpr) {
				// Can handle MINUS and DIV here
				return op(f1, ((DoubleExpr) f2)._dConstVal, op);
			} else if (f1 instanceof OperExpr && f2 instanceof OperExpr
					&& ((OperExpr) f1)._type == ((OperExpr) f2)._type
					&& ((OperExpr) f1)._type == op && (op == SUM || op == PROD)) {
				// Exploit associativity
				ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>(
						((OperExpr) f1)._terms);
				terms.addAll(((OperExpr) f2)._terms);
				return new OperExpr(op, terms);
			} else {
				ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>();
				terms.add(f1);
				terms.add(f2);
				return new OperExpr(op, terms);
			}

		}

		public static ArithExpr op(ArithExpr f1, double d, int op) {
			if (f1 instanceof DoubleExpr) {
				if (op == SUM)
					return new DoubleExpr(((DoubleExpr) f1)._dConstVal + d);
				else if (op == PROD)
					return new DoubleExpr(((DoubleExpr) f1)._dConstVal * d);
				else if (op == MINUS)
					return new DoubleExpr(((DoubleExpr) f1)._dConstVal - d);
				else if (op == DIV)
					return new DoubleExpr(((DoubleExpr) f1)._dConstVal / d);
				else {
					ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>();
					terms.add(new DoubleExpr(d));
					terms.add(f1);
					return new OperExpr(op, terms);
				}
			} else if (f1 instanceof OperExpr && ((OperExpr) f1)._type == op
					&& (op == SUM || op == PROD)) {
				ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>(
						((OperExpr) f1)._terms);
				terms.add(new DoubleExpr(d));
				return new OperExpr(op, terms);
			} else {
				ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>();
				terms.add(f1);
				terms.add(new DoubleExpr(d));
				return new OperExpr(op, terms);
			}
		}

	/*	public static ArithExpr sqrt(ArithExpr f1) {
			if (f1 instanceof DoubleExpr)
				return new DoubleExpr(Math.sqrt((((DoubleExpr) f1)._dConstVal)));
			else {

				String result = "sqrt" + f1.toString();
				return ArithExpr.parse(result);
			}

		}*/

		public abstract ArithExpr substitute(HashMap<String, ArithExpr> subst);

		public abstract Double evaluate(HashMap<String, Double> cont_assign);

		public abstract Double evaluateRange(
				HashMap<String, Double> low_assign,
				HashMap<String, Double> high_assign, boolean use_low);

		public abstract void collectVars(HashSet<String> vars);
		
		// Assume expression is canonical, hence in sum of products form (could be a single term)
				public ArithExpr differentiateExpr(String diff_var) {
					diff_var = diff_var.intern();
					ArithExpr ret_expr = null;
					if (this instanceof OperExpr && ((OperExpr) this)._type == SUM) {
						ret_expr = ((OperExpr) this).differentiateMultipleTerms(diff_var);
					} else if (this instanceof OperExpr && ((OperExpr) this)._type == PROD) {
						ret_expr = ((OperExpr) this).differentiateTerm(diff_var);
					} else if ((this instanceof VarExpr) || (this instanceof DoubleExpr)) {
						OperExpr temp = new OperExpr(PROD, Arrays.asList(this));
						ret_expr = temp.differentiateTerm(diff_var);
					} else {
						System.out.println("differentiateLeaf: Unsupported expression '" + this + "'");
						System.exit(1);
					}
					return ret_expr;
				}

				// Assume expression is canonical, hence in sum of products form (could be a single term)
				public ArithExpr integrateExpr(String integration_var) {
					integration_var = integration_var.intern();
					ArithExpr ret_expr = null;
					if (this instanceof OperExpr && ((OperExpr) this)._type == SUM) {
						ret_expr = ((OperExpr) this).integrateMultipleTerms(integration_var);
					} else if (this instanceof OperExpr && ((OperExpr) this)._type == PROD) {
						ret_expr = ((OperExpr) this).integrateTerm(integration_var);
					} else if ((this instanceof VarExpr) || (this instanceof DoubleExpr)) {
						OperExpr temp = new OperExpr(PROD, Arrays.asList(this));
						ret_expr = temp.integrateTerm(integration_var);
					} else {
						System.out.println("processXADDLeaf: Unsupported expression '" + this + "'");
						System.exit(1);
					}
					return ret_expr;
				}

				// Takes ArithExpr expr1 linear in var, returns (coef,expr2) where expr1 = coef*x + expr2
				// Assume expression is canonical, hence in sum of products form (could be a single term)
				public CoefExprPair removeVarFromExpr(String remove_var) {
					remove_var = remove_var.intern();
					CoefExprPair ret = null;
					if (this instanceof OperExpr && ((OperExpr) this)._type == SUM) {
						ret = ((OperExpr) this).removeVarFromExprMultipleTerms(remove_var);
					} else if (this instanceof OperExpr && ((OperExpr) this)._type == PROD) {
						ret = ((OperExpr) this).removeVarFromExprTerm(remove_var);
					} else if ((this instanceof VarExpr) || (this instanceof DoubleExpr)) {
						OperExpr temp = new OperExpr(PROD, Arrays.asList(this));
						ret = temp.removeVarFromExprTerm(remove_var);
					} else {
						System.out.println("removeVarFromExpr: Unsupported expression '" + this + "'");
						System.exit(1);
					}
					return ret;
				}

				// Assume expression is canonical, hence in sum of products form (could be a single term)
				public int determineHighestOrderOfVar(String var) {
					var = var.intern();
					CoefExprPair ret = null;
					if (this instanceof OperExpr && ((OperExpr) this)._type == SUM) {
						return ((OperExpr) this).determineHighestOrderOfVarMultipleTerms(var);
					} else if (this instanceof OperExpr && ((OperExpr) this)._type == PROD) {
						return ((OperExpr) this).determineHighestOrderOfVarTerm(var);
					} else if ((this instanceof VarExpr) || (this instanceof DoubleExpr)) {
						OperExpr temp = new OperExpr(PROD, Arrays.asList(this));
						return temp.determineHighestOrderOfVarTerm(var);
					} else {
						System.out.println("removeVarFromExpr: Unsupported expression '" + this + "'");
						System.exit(1);
						return 0;
					}
				}
		
		
		
	}

	public static class OperExpr extends ArithExpr implements Serializable{

		public int _type = UND;
		public ArrayList<ArithExpr> _terms = null;

		public OperExpr(int type, ArithExpr t1, ArithExpr t2) {
			// this(type, Arrays.asList(new ArithExpr[] {t1, t2}));
			this(type, Arrays.asList(t1, t2));
		}

		public OperExpr(int type, List<ArithExpr> terms) {
			_type = type;

			// Ensure subtraction and division are binary operators
			if ((_type == MINUS || _type == DIV) && terms.size() != 2) {
				_type = ERROR;
				return;
			}

			_terms = new ArrayList<ArithExpr>(terms);
			if (_type == SUM || _type == PROD)
				Collections.sort(_terms);

		}

		public boolean equals(Object o) {
			if (o instanceof OperExpr) {
				OperExpr e = (OperExpr) o;
				return this._type == e._type && this._terms.equals(e._terms);
			} else
				return false;
		}

		public int hashCode() {
			return _terms.toString().hashCode() - _type;
		}
		
		public OperExpr clone()
		{
			OperExpr opr =  new OperExpr(UND, new ArrayList<XADD.ArithExpr>());
			opr._type = new Integer(this._type);
			//opr._terms = new ArrayList<XADD.ArithExpr>();
			for (int i=0;i<this._terms.size();i++)
			{
				//opr._terms.add(SerialClone.clone(this._terms.get(i)));
				opr._terms.add((ArithExpr) this._terms.get(i).clone());
			}
			return opr;
		}

		public static int Convert2XADD(XADD context, FOPC.TFunction t) {

			if (t._nArity == 0)
				return context.getTermNode(new VarExpr(t._sFunName));

			if (t._sFunName.equals("N") && t._nArity == 4) {

				ArithExpr expr = ArithExpr.Convert2ArithExpr(t.getBinding(0));
				ArithExpr mu = ArithExpr.Convert2ArithExpr(t.getBinding(1));
				ArithExpr var = ArithExpr.Convert2ArithExpr(t.getBinding(2));
				ArithExpr width = ArithExpr.Convert2ArithExpr(t.getBinding(3)); // truncated
				// outside
				// of
				// +/-
				// width

				if (!(var instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant variance: "
							+ var.toString());
					System.exit(1);
				}
				double dvar = ((DoubleExpr) var)._dConstVal;

				if (!(width instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant width: "
							+ width.toString());
					System.exit(1);
				}
				double dwidth = ((DoubleExpr) width)._dConstVal;

				double Z = 3d / (4d * dwidth * dwidth * dwidth);
				double DW2 = dwidth * dwidth;
				String s = "([" + expr + " >= " + mu + " - " + dwidth + "] "
						+ "([" + expr + " <= " + mu + " + " + dwidth + "] "
						+ "( [" + _df.format(Z) + " * " + "(-((" + expr + " - "
						+ mu + ") * (" + expr + " - " + mu + ")) + " + DW2
						+ ")] )" + "( [0.0] ) ) ( [0.0] ) )";
				// String s = "([7.0])";

				// System.out.println("Produced: " + s);

				ArrayList l = HierarchicalParser.ParseString(s);
				// System.out.println("Parsed: " + l);
				int dd = context.buildCanonicalXADD((ArrayList) l.get(0));
				return dd;

			} else if (t._sFunName.equals("U") && t._nArity == 4) {

				ArithExpr expr = ArithExpr.Convert2ArithExpr(t.getBinding(0));
				ArithExpr mu = ArithExpr.Convert2ArithExpr(t.getBinding(1));
				ArithExpr widthl = ArithExpr.Convert2ArithExpr(t.getBinding(2)); // width
				// left
				ArithExpr widthr = ArithExpr.Convert2ArithExpr(t.getBinding(3)); // width
				// right

				if (!(widthl instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant variance: "
							+ widthl.toString());
					System.exit(1);
				}
				double dwidthl = ((DoubleExpr) widthl)._dConstVal;

				if (!(widthr instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant width: "
							+ widthr.toString());
					System.exit(1);
				}
				double dwidthr = ((DoubleExpr) widthr)._dConstVal;

				if (dwidthl < 0 || dwidthr < 0) {
					System.out.println("Negative widths (" + dwidthl + ","
							+ dwidthr + ") not allowed.");
					System.exit(1);
				}

				double Z = 1d / (dwidthl + dwidthr);
				String s = "([" + expr + " >= " + mu + " - " + dwidthl + "] "
						+ "([" + expr + " <= " + mu + " + " + dwidthr + "] "
						+ "( [" + _df.format(Z) + "] )"
						+ "( [0.0] ) ) ( [0.0] ) )";
				ArrayList l = HierarchicalParser.ParseString(s);
				int dd = context.buildCanonicalXADD((ArrayList) l.get(0));
				return dd;

			} else if (t._sFunName.equals("T") && t._nArity == 4) {

				ArithExpr expr = ArithExpr.Convert2ArithExpr(t.getBinding(0));
				ArithExpr mu = ArithExpr.Convert2ArithExpr(t.getBinding(1));
				ArithExpr widthl = ArithExpr.Convert2ArithExpr(t.getBinding(2)); // width
				// left
				ArithExpr widthr = ArithExpr.Convert2ArithExpr(t.getBinding(3)); // width
				// right

				if (!(widthl instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant variance: "
							+ widthl.toString());
					System.exit(1);
				}
				double dwidthl = ((DoubleExpr) widthl)._dConstVal;

				if (!(widthr instanceof DoubleExpr)) {
					System.out
					.println("Currently cannot handle non-constant width: "
							+ widthr.toString());
					System.exit(1);
				}
				double dwidthr = ((DoubleExpr) widthr)._dConstVal;

				if (dwidthl < 0 || dwidthr < 0) {
					System.out.println("Negative widths (" + dwidthl + ","
							+ dwidthr + ") not allowed.");
					System.exit(1);
				}

				double H = 2d / (dwidthr + dwidthl);
				String s = null;

				// Handle cases where left- or right-hand sides are empty
				if (dwidthl == 0d) {
					s = "([" + expr + " >= " + mu + "] " + "([" + expr + " <= "
							+ mu + " + " + dwidthr + "] " + "( ["
							+ _df.format(-H / dwidthr) + " * " + "(" + expr
							+ " - " + mu + " - " + widthr + ")] )"
							+ "( [0.0] ) ) ( [0.0] ) )";
				} else if (dwidthr == 0d) {
					s = "([" + expr + " >= " + mu + " - " + dwidthl + "] "
							+ "([" + expr + " <= " + mu + "] " + "( ["
							+ _df.format(H / dwidthl) + " * " + "(" + expr
							+ " - " + mu + " + " + widthl + ")] )"
							+ "( [0.0] ) ) ( [0.0] ) )";
				} else {
					s = "([" + expr + " >= " + mu + " - " + dwidthl + "] "
							+ "([" + expr + " <= " + mu + " + " + dwidthr
							+ "] " + "([" + expr + " <= " + mu + "] " + "( ["
							+ _df.format(H / dwidthl) + " * " + "(" + expr
							+ " - " + mu + " + " + widthl + ")] )" + "( ["
							+ _df.format(-H / dwidthr) + " * " + "(" + expr
							+ " - " + mu + " - " + widthr + ")] ))"
							+ "( [0.0] ) ) ( [0.0] ) )";
				}

				ArrayList l = HierarchicalParser.ParseString(s);
				int dd = context.buildCanonicalXADD((ArrayList) l.get(0));
				return dd;

			} else if (t._nArity == 2) {

				// A standard operator expression convertible to a terminal node
				// The following is a bit ugly but easy to write & debug and
				// only called once when files are read (so inefficiency is OK)
				int xadd1 = Convert2XADD(context, t.getBinding(0));
				int xadd2 = Convert2XADD(context, t.getBinding(1));
				int op = UND;
				if (t._sFunName.equals("f_add")) {
					op = SUM;
				} else if (t._sFunName.equals("f_sub")) {
					op = MINUS;
				} else if (t._sFunName.equals("f_mul")) {
					op = PROD;
				} else if (t._sFunName.equals("f_div")) {
					op = DIV;
				} else {
					System.err
					.println("Convert2XADD: Could not process binary function: "
							+ t.toFOLString());
					System.exit(1);
				}
				return context.apply(xadd1, xadd2, op);
			} else {
				System.err.println("Convert2XADD: Could not process: "
						+ t.toFOLString());
				System.exit(1);
				return -1;
			}
		}

		public static ArithExpr Convert2OperExpr(FOPC.TFunction t) {
			// System.out.println("Convert2OperExpr: [" + t._nArity + "] "
			// + t.toFOLString());
			if (t._nArity == 0)
				return new VarExpr(t._sFunName);

			// The following is a bit ugly but easy to write & debug and
			// only called once when files are read (so inefficiency is OK)
			ArithExpr term1 = ArithExpr.Convert2ArithExpr(t.getBinding(0));
			ArithExpr term2 = ArithExpr.Convert2ArithExpr(t.getBinding(1));
			ArrayList<ArithExpr> terms = new ArrayList<ArithExpr>();
			int type = UND;
			if (t._sFunName.equals("f_add")) {
				type = SUM;
			} else if (t._sFunName.equals("f_sub")) {
				type = MINUS;
				if (term1 instanceof DoubleExpr && term2 instanceof DoubleExpr
						&& ((DoubleExpr) term1)._dConstVal == 0d)
					return new DoubleExpr(-((DoubleExpr) term2)._dConstVal);
			} else if (t._sFunName.equals("f_mul")) {
				type = PROD;
			} else if (t._sFunName.equals("f_div")) {
				type = DIV;
			}
			if (type == UND)
				return null;
			if ((type == SUM || type == PROD) && (term1 instanceof OperExpr)
					&& ((OperExpr) term1)._type == type) {
				terms.addAll(((OperExpr) term1)._terms);
				term1 = null;
			}
			if ((type == SUM || type == PROD) && (term2 instanceof OperExpr)
					&& ((OperExpr) term2)._type == type) {
				terms.addAll(((OperExpr) term2)._terms);
				term2 = null;
			}
			if (term1 != null)
				terms.add(term1);
			if (term2 != null)
				terms.add(term2);
			return new OperExpr(type, terms);
		}

		public String toString(boolean format) {
			StringBuilder sb = new StringBuilder("(");
			for (int i = 0; i < _terms.size(); i++) {
				if (i != 0)
					sb.append(" " + _aOpNames[_type] + " ");
				sb.append(_terms.get(i).toString(format));
			}
			sb.append(")");
			return sb.toString();
		}

		public void collectVars(HashSet<String> vars) {
			for (ArithExpr e : _terms)
				e.collectVars(vars);
		}

		public ArithExpr substitute(HashMap<String, ArithExpr> subst) {
			ArrayList<ArithExpr> terms2 = new ArrayList<ArithExpr>();
			for (ArithExpr expr : _terms)
				terms2.add(expr.substitute(subst));
			OperExpr expr = new OperExpr(_type, terms2);
			if (expr._terms.size() == 1)
				return expr._terms.get(0);
			else
				return expr;
		}

		public Double evaluate(HashMap<String, Double> cont_assign) {
			Double accum = _terms.get(0).evaluate(cont_assign);
			for (int i = 1; i < _terms.size() && accum != null; i++) {
				Double term_eval = _terms.get(i).evaluate(cont_assign);
				if (term_eval == null)
					accum = null;
				else
					switch (_type) {
					case SUM:
						accum = accum + term_eval;
						break;
					case MINUS:
						accum = accum - term_eval;
						break;
					case PROD:
						accum = accum * term_eval;
						break;
					case DIV:
						accum = accum / term_eval;
						break;
					default:
						accum = null;
					}
			}
			return accum;
		}

		@Override
		public Double evaluateRange(HashMap<String, Double> low_assign,
				HashMap<String, Double> high_assign, boolean use_low) {

			// Must use canonical nodes here... assumes products are binary
			// with the first term being a coefficient
			if (!USE_CANONICAL_NODES) {
				System.err
				.println("Must use canonical nodes if using evaluateRange");
				System.exit(1);
			}

			if (DEBUG_EVAL_RANGE)
				System.out.println("Evaluating " + (use_low ? "min" : "max")
						+ " range: " + this);

			HashMap<String, Double> assign = use_low ? low_assign : high_assign;
			Double accum = _terms.get(0).evaluateRange(low_assign, high_assign,
					use_low);
			if (DEBUG_EVAL_RANGE)
				System.out.println("- Term eval [" + 0 + "] = " + _terms.get(0)
						+ " = " + accum + " -- " + use_low);

			boolean subterm_use_low = (_type == MINUS || _type == DIV || (_type == PROD && accum < 0d)) ? !use_low
					: use_low;

			for (int i = 1; i < _terms.size() && accum != null; i++) {

				Double term_eval = _terms.get(i).evaluateRange(low_assign,
						high_assign, subterm_use_low);
				if (DEBUG_EVAL_RANGE)
					System.out.println("- Term eval [" + i + "] = "
							+ _terms.get(i) + " = " + term_eval + " -- "
							+ subterm_use_low);
				if (term_eval == null)
					accum = null;
				else
					switch (_type) {
					case SUM:
						accum += term_eval;
						break;
					case MINUS:
						accum -= term_eval;
						break;
					case PROD:
						accum *= term_eval;
						break;
					case DIV:
						accum /= term_eval;
						break;
					default:
						accum = null;
					}
				if (DEBUG_EVAL_RANGE)
					System.out.println("- accum: " + accum);
			}
			if (DEBUG_EVAL_RANGE)
				System.out.println("* Result " + (use_low ? "min" : "max")
						+ " range: " + accum);
			return accum;
		}

		public boolean checkCanonical() {

			// This node is canonical if it is term canonical
			// or it is a sum of terms
			if (checkTermCanonical())
				return true;

			if (_type == SUM) {
				// Ensure all subterms are canonical
				for (int i = 0; i < _terms.size(); i++) {

					// First term can be a constant so long as more than one
					// term
					if (i == 0 && (_terms.get(0) instanceof DoubleExpr)) {
						if (Math.abs(((DoubleExpr) _terms.get(0))._dConstVal) <= 1e-6d)
							return false;
						else
							continue;
					}

					if (!(_terms.get(i) instanceof OperExpr)
							|| !((OperExpr) _terms.get(i)).checkTermCanonical()) {
						// System.out.println("-- not canonical because [" + i +
						// "]" + _terms.get(i) + " : " +
						// _terms.get(i).getClass());
						return false;
					}
				}

				return true;
			} else {
				// System.out.println("-- not canonical because not SUM: " +
				// _aOpNames[_type]);
				return false;
			}
		}

		public boolean checkTermCanonical() {
			// This is term canonical if it is a product of a constant followed
			// by variables
			if (_type == PROD) {
				if (!(_terms.get(0) instanceof DoubleExpr))
					return false;

				for (int i = 1; i < _terms.size(); i++) {
					if (!(_terms.get(i) instanceof VarExpr))
						return false;
				}

				return true;
			} else
				return false;
		}

		// Canonicity for arithmetic expressions:
		//
		// 1. Expressions all zero on RHS of comparisons and restrict symbols:
		// a > b : a <= b and swap branches
		// a < b : a >= b and swap branches
		// a != b : a == b and swap branches
		// 2. Multiple layers of + / * collapsed: (X + Y) + Z -> X + Y + Z
		// 3. Distribute * over +: X * (A + B) -> X * A + X * B
		// 4. All subtraction: X - Y -> X + -Y
		// ??? 5. Division -> multiplication
		// ??? 6. Multiple multipled divisions -> numerator and denominator
		// 7. Sorting of OperExpr terms with TreeSet?
		// 8. Make all products start with a single Double coefficient
		// 9. Compress / remove common polynomial terms
		// 10. Prevent singleton operator expressions
		public static int ALREADY_CANONICAL = 0;
		public static int NON_CANONICAL = 0;

		public Expr makeCanonical() {

			// A simple non-canonical case is OperExpr - 0, so catch this
			if (_type == MINUS && _terms.get(1) instanceof DoubleExpr
					&& ((DoubleExpr) _terms.get(1))._dConstVal == 0d) {
				return _terms.get(0).makeCanonical();
			}

			// If already canonical, no need to modify
			if (checkCanonical()) {
				// System.out.println("** Already canonical: " + this);
				ALREADY_CANONICAL++;
				return this;
			} else {
				// System.out.println("** Not canonical: " + this);
				NON_CANONICAL++;
			}

			int new_type = _type;
			ArrayList<ArithExpr> new_terms = new ArrayList<ArithExpr>(_terms);

			// 4. All subtraction: X - Y -> X + -Y
			if (new_type == MINUS) {
				ArithExpr term2 = new_terms.get(1);
				term2 = ArithExpr.op(term2, NEG_ONE, PROD);
				new_terms.set(1, term2);
				new_type = SUM;
			}

			// Recursively ensure all subterms in canonical form, and then
			// 2. Multiple layers of + / * collapsed: (X + Y) + Z -> X + Y + Z
			ArrayList<ArithExpr> reduced_terms = new ArrayList<ArithExpr>();
			for (ArithExpr e : new_terms) {
				e = (ArithExpr) e.makeCanonical();
				// If same type, add all subterms directly to reduced terms
				if ((e instanceof OperExpr) && ((OperExpr) e)._type == new_type
						&& (new_type == SUM || new_type == PROD))
					reduced_terms.addAll(((OperExpr) e)._terms);
				else
					reduced_terms.add(e);
			}
			new_terms = reduced_terms;
			// System.out.println(">> Flattened terms: " + reduced_terms);

			// 3. Distribute * over +: X * (A + B) -> X * A + X * B
			// X * (1/Y) * (W + Z) * (U + V)
			// Maintain sum list...
			// if division, multiply in 1/x
			if (new_type == PROD) {

				ArrayList<ArithExpr> sum_terms = new ArrayList<ArithExpr>();
				ArithExpr first_term = new_terms.get(0);
				if ((first_term instanceof OperExpr)
						&& ((OperExpr) first_term)._type == SUM)
					sum_terms.addAll(((OperExpr) first_term)._terms);
				else
					sum_terms.add(first_term);

				for (int i = 1; i < new_terms.size(); i++) {
					ArithExpr e = new_terms.get(i);
					if ((e instanceof OperExpr) && ((OperExpr) e)._type == SUM) {
						// e2 : {A + B} * e3 : {C + D}
						// System.out.println(">>>> Mult 1 " + e + " * " +
						// sum_terms);
						ArrayList<ArithExpr> new_sum_terms = new ArrayList<ArithExpr>();
						for (ArithExpr e2 : sum_terms) {
							for (ArithExpr e3 : ((OperExpr) e)._terms) {
								// System.out.println(">>>> Multiplying " + e2 +
								// " * " + e3);
								new_sum_terms.add(ArithExpr.op(e2, e3, PROD));
							}
						}
						// System.out.println(">>>> Mult 1 Out " +
						// new_sum_terms);
						sum_terms = new_sum_terms;
					} else {
						// e2 : {A + B} * e
						// System.out.println(">>>> Mult 2 " + e + " * " +
						// sum_terms);
						for (int j = 0; j < sum_terms.size(); j++) {
							ArithExpr e2 = sum_terms.get(j);
							sum_terms.set(j, new OperExpr(PROD, e, e2));
						}
					}
				}

				// If sum_terms are singular no need to modify, otherwise
				if (sum_terms.size() > 1) {

					new_type = SUM;

					// Again make canonical and collapse terms where possible
					new_terms.clear();
					for (ArithExpr e : sum_terms) {
						e = (ArithExpr) e.makeCanonical();
						// If same type, add all subterms directly to reduced
						// terms
						if ((e instanceof OperExpr)
								&& ((OperExpr) e)._type == SUM)
							new_terms.addAll(((OperExpr) e)._terms);
						else
							new_terms.add(e);
					}
				}
			}

			// 9. Merge (and remove) all polynomial terms in a sum
			if (new_type == SUM) {
				ArrayList<ArithExpr> non_terms = new ArrayList<ArithExpr>();
				double const_sum = 0d;

				// Hash all terms to a coefficient
				HashMap<ArrayList<ArithExpr>, Double> term2coef = new HashMap<ArrayList<ArithExpr>, Double>();
				for (ArithExpr e : new_terms) {
					if ((e instanceof OperExpr && ((OperExpr) e)._type == PROD)
							|| (e instanceof VarExpr)) {

						// Determine the terms and coefficient
						ArrayList<ArithExpr> index = new ArrayList<ArithExpr>();
						DoubleExpr d = null;
						if (e instanceof VarExpr) {
							index.add(e);
							d = new DoubleExpr(1d);
						} else {
							OperExpr o = (OperExpr) e;
							d = (DoubleExpr) o._terms.get(0);
							for (int j = 1; j < o._terms.size(); j++)
								index.add(o._terms.get(j));
						}

						// Hash to the correct coefficient
						Double dval = null;
						if ((dval = term2coef.get(index)) != null)
							dval += d._dConstVal;
						else
							dval = d._dConstVal;
						term2coef.put(index, dval);

					} else if (e instanceof DoubleExpr) {
						const_sum += ((DoubleExpr) e)._dConstVal;
					} else
						non_terms.add(e);
				}

				// Convert back to an ArrayList
				new_terms = non_terms;
				if (const_sum != 0d)
					new_terms.add(0, new DoubleExpr(const_sum));

				for (Map.Entry<ArrayList<ArithExpr>, Double> t : term2coef
						.entrySet()) {
					double val = t.getValue();
					if (val == 0d)
						continue;

					ArrayList<ArithExpr> term = t.getKey();
					DoubleExpr dcoef = new DoubleExpr(val);
					term.add(0, dcoef);
					new_terms.add(new OperExpr(PROD, term));
				}

				// An empty sum is zero
				if (new_terms.size() == 0)
					return new DoubleExpr(0d);
			}

			// 8. Make all products start with a single Double coefficient
			if (new_type == PROD) {
				double coef = 1d;
				ArrayList<ArithExpr> factors = new ArrayList<ArithExpr>();
				for (ArithExpr e : new_terms) {
					if (e instanceof DoubleExpr)
						coef *= ((DoubleExpr) e)._dConstVal;
					else
						factors.add(e);
				}
				if (coef != 0d) {
					factors.add(0, new DoubleExpr(coef));
					new_terms = factors; // Will be sorted on new OperExpr
				} else {
					return new DoubleExpr(0d);
				}
			}
			// Handle division of two constants
			if (new_type == DIV && new_terms.get(0) instanceof DoubleExpr
					&& new_terms.get(1) instanceof DoubleExpr) {
				return new DoubleExpr(
						((DoubleExpr) new_terms.get(0))._dConstVal
						/ ((DoubleExpr) new_terms.get(1))._dConstVal);
			}

			// 10. Prevent singleton operator expressions
			if (new_terms.size() == 1) {
				return new_terms.get(0);
			}

			// Ensure canonical order
			OperExpr canonical_expr = new OperExpr(new_type, new_terms);
			// System.out.println("- now canonical: " + canonical_expr);
			return canonical_expr;
		}

		@Override
		public String toString() {
			return toString(true);
		}
		
		
		// Must be a SUM of terms to get here
				public OperExpr differentiateMultipleTerms(String diff_var) {
					if (this._type != SUM) {
						System.out.println("differentiateMultipleTerms: Expected SUM, got '" + this + "'");
						System.exit(1);
					}
					ArrayList<ArithExpr> differentiated_terms = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof OperExpr) {
							differentiated_terms.add(((OperExpr) e).differentiateTerm(diff_var));
						} else if ((e instanceof VarExpr) || (e instanceof DoubleExpr)) {
							OperExpr temp = new OperExpr(PROD, Arrays.asList(e));
							differentiated_terms.add(temp.differentiateTerm(diff_var));
						} else {
							System.out.println("differentiateMultipleTerms: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}
					return new OperExpr(SUM, differentiated_terms);
				}

				// A single term (PROD)
				public ArithExpr differentiateTerm(String diff_var) {
					if (this._type != PROD) {
						System.out.println("differentiateTerm: Expected PROD, got '" + this + "'");
						System.exit(1);
					}

					// Process all terms (optional double followed by vars)
					int derivative_var_count = 0;
					int last_var_added_at = -1;
					DoubleExpr d = new DoubleExpr(1d);
					ArrayList<ArithExpr> factors = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof DoubleExpr) {
							DoubleExpr d2 = (DoubleExpr) e;
							d = new DoubleExpr(d._dConstVal * d2._dConstVal);
						} else if (e instanceof VarExpr) {
							factors.add(e);
							// Both interned so we can test direct equality
							if (((VarExpr) e)._sVarName == diff_var) {
								derivative_var_count++;
								last_var_added_at = factors.size() - 1;
							}
						} else {
							System.out.println("differentiateTerm: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}

					// Perform differentiation
					if (derivative_var_count == 0) {
						return ZERO; // Derivative of a constant is 0
					} else {
						// x*x*...*x = x^n
						// d/dx x^n = n*x^{n-1}
						factors.remove(last_var_added_at);
						d = new DoubleExpr(((double) derivative_var_count) * d._dConstVal);
						factors.add(0, d);

						return new OperExpr(PROD, factors);
					}
				}

				// Must be a SUM of terms to get here
				public OperExpr integrateMultipleTerms(String integration_var) {
					if (this._type != SUM) {
						System.out.println("integrateMultipleTerms: Expected SUM, got '" + this + "'");
						System.exit(1);
					}
					ArrayList<ArithExpr> integrated_terms = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof OperExpr) {
							integrated_terms.add(((OperExpr) e).integrateTerm(integration_var));
						} else if ((e instanceof VarExpr) || (e instanceof DoubleExpr)) {
							OperExpr temp = new OperExpr(PROD, Arrays.asList(e));
							integrated_terms.add(temp.integrateTerm(integration_var));
						} else {
							System.out.println("integrateMultipleTerms: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}
					return new OperExpr(SUM, integrated_terms);
				}

				// A single term (PROD)
				public ArithExpr integrateTerm(String integration_var) {
					if (this._type != PROD) {
						System.out.println("integrateTerm: Expected PROD, got '" + this + "'");
						System.exit(1);
					}

					// Process all terms (optional double followed by vars)
					int integration_var_count = 0;
					DoubleExpr d = new DoubleExpr(1d);
					ArrayList<ArithExpr> factors = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						// while (e instanceof OperExpr) {
						// OperExpr oe = (OperExpr) e;
						// e = e.op(oe._terms.get(0), oe._terms.get(1), oe._type);
						// }
						if (e instanceof DoubleExpr) {
							DoubleExpr d2 = (DoubleExpr) e;
							d = new DoubleExpr(d._dConstVal * d2._dConstVal);
						} else if (e instanceof VarExpr) {
							factors.add(e);
							// Both interned so we can test direct equality
							if (((VarExpr) e)._sVarName == integration_var)
								integration_var_count++;
						} else {
							System.out.println("integrateTerm: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}

					// Perform integration
					factors.add(new VarExpr(integration_var));
					d = new DoubleExpr(d._dConstVal / (double) (integration_var_count + 1));
					factors.add(0, d);

					return new OperExpr(PROD, factors);
				}

				// Must be a SUM of terms to get here
				public CoefExprPair removeVarFromExprMultipleTerms(String remove_var) {
					if (this._type != SUM) {
						System.out.println("removeVarFromExprMultipleTerms: Expected SUM, got '" + this + "'");
						System.exit(1);
					}
					double var_coef = 0d;
					ArrayList<ArithExpr> remaining_terms = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof OperExpr) {
							CoefExprPair p = ((OperExpr) e).removeVarFromExprTerm(remove_var);
							var_coef += p._coef;
							remaining_terms.add(p._expr);
						} else if (e instanceof VarExpr) {
							OperExpr temp = new OperExpr(PROD, Arrays.asList(e));
							CoefExprPair p = temp.removeVarFromExprTerm(remove_var);
							var_coef += p._coef;
							remaining_terms.add(p._expr);
						} else if (e instanceof DoubleExpr) {
							remaining_terms.add(e);
						} else {
							System.out.println("removeVarFromExprMultipleTerms: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}
					return new CoefExprPair(new OperExpr(SUM, remaining_terms), var_coef);
				}

				// A single term (PROD)
				public CoefExprPair removeVarFromExprTerm(String remove_var) {
					double var_coef = 0d;
					if (this._type != PROD) {
						System.out.println("removeVarFromExprTerm: Expected PROD, got '" + this + "'");
						System.exit(1);
					}

					// Process all terms (optional double followed by vars)
					int remove_var_count = 0;
					double coef = 1d;
					ArrayList<ArithExpr> factors = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof DoubleExpr) {
							coef *= ((DoubleExpr) e)._dConstVal;
						} else if (e instanceof VarExpr) {
							// Both interned so we can test direct equality
							if (((VarExpr) e)._sVarName == remove_var)
								remove_var_count++;
							else
								factors.add(e);
						} else {
							System.out.println("removeVarFromExprTerm: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}

					// Check for proper form
					if (remove_var_count > 0) {
						if (remove_var_count > 1 || factors.size() > 0) {
							System.out.println("removeVarFromExprTerm: var '" + remove_var
									+ "' must appear linearly in expression '" + this + "'");
							System.exit(1);
						}
						// If get here only coef*_integrationVar
						var_coef += coef;
						return new CoefExprPair(ZERO, var_coef); // Just add a zero term in this place
					} else {
						factors.add(0, new DoubleExpr(coef));
						return new CoefExprPair(new OperExpr(PROD, factors), var_coef);
					}
				}

				// Must be a SUM of terms to get here
				public int determineHighestOrderOfVarMultipleTerms(String var) {
					if (this._type != SUM) {
						System.out.println("determineHighestOrderOfVarMultipleTerms: Expected SUM, got '" + this + "'");
						System.exit(1);
					}
					int max_order = 0;
					for (ArithExpr e : this._terms) {
						if (e instanceof OperExpr) {
							max_order = Math.max(max_order, ((OperExpr) e).determineHighestOrderOfVarTerm(var));
						} else if (e instanceof VarExpr) {
							OperExpr temp = new OperExpr(PROD, Arrays.asList(e));
							max_order = Math.max(max_order, temp.determineHighestOrderOfVarTerm(var));
						} else if (!(e instanceof DoubleExpr)) {
							System.out.println("determineHighestOrderOfVarMultipleTerms: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}
					return max_order;
				}

				// A single term (PROD)
				public int  determineHighestOrderOfVarTerm(String var) {
					double var_coef = 0d;
					if (this._type != PROD) {
						System.out.println("determineHighestOrderOfVarTerm: Expected PROD, got '" + this + "'");
						System.exit(1);
					}

					// Process all terms (optional double followed by vars)
					int integration_var_count = 0;
					double coef = 1d;
					ArrayList<ArithExpr> factors = new ArrayList<ArithExpr>();
					for (ArithExpr e : this._terms) {
						if (e instanceof DoubleExpr) {
							coef *= ((DoubleExpr) e)._dConstVal;
						} else if (e instanceof VarExpr) {
							// Both interned so we can test direct equality
							if (((VarExpr) e)._sVarName == var)
								integration_var_count++;
							else
								factors.add(e);
						} else {
							System.out.println("determineHighestOrderOfVarTerm: Unsupported expression '" + e + "'");
							System.exit(1);
						}
					}
					return integration_var_count;
				}
			}


	public static class DoubleExpr extends ArithExpr implements Serializable {
		public double _dConstVal = Double.NaN;

		public DoubleExpr(double val) {
			// *10000d, truncate, /10000d
			/*val = val * 1000d;
			val = Math.floor(val);
			val = val /1000d;*/
			_dConstVal = val;
			//_dConstVal = (double) Math.round(val*1000d)/1000d;
		}


		public String toString() {
			return _df.format(_dConstVal);
		}

		@Override
		public String toString(boolean format) {
			return _df_unformatted.format(_dConstVal);
		}

		public boolean equals(Object o) {
			if (o instanceof DoubleExpr) {
				DoubleExpr d = (DoubleExpr) o;
				return this._dConstVal == d._dConstVal;
			} else
				return false;
		}
		
		public DoubleExpr clone()
		{
			DoubleExpr dbx = new DoubleExpr(Double.NaN);
			dbx._dConstVal = new Double(_dConstVal);
			return dbx;
		}

		public int hashCode() {
			return Float.floatToIntBits((float) _dConstVal);
		}

		public ArithExpr substitute(HashMap<String, ArithExpr> subst) {
			return this;
		}

		public Double evaluate(HashMap<String, Double> cont_assign) {
			return _dConstVal;
		}

		@Override
		public Double evaluateRange(HashMap<String, Double> low_assign,
				HashMap<String, Double> high_assign, boolean use_low) {
			return _dConstVal;
		}

		public void collectVars(HashSet<String> vars) {
		}

		public Expr makeCanonical() {
			return this;
		}

	}

	public static class VarExpr extends ArithExpr implements Serializable{
		public String _sVarName = null;
		public int _nHashCode = -1;

		public VarExpr(String name) {
			_sVarName = name.intern();
			_nHashCode = _sVarName.hashCode();
		}

		public String toString() {
			return _sVarName;
		}

		public int hashCode() {
			return _nHashCode;
		}

		public boolean equals(Object o) {
			if (o instanceof VarExpr) {
				VarExpr v = (VarExpr) o;
				return this._sVarName == v._sVarName;
			} else
				return false;
		}

		public VarExpr clone()
		{
			VarExpr vrx =  new VarExpr( new String(this._sVarName));
			return vrx;
		} 
		
		public ArithExpr substitute(HashMap<String, ArithExpr> subst) {
			ArithExpr v = subst.get(_sVarName);
			return v != null ? v : this;
		}

		public Double evaluate(HashMap<String, Double> cont_assign) {
			return cont_assign.get(_sVarName);
		}

		@Override
		public Double evaluateRange(HashMap<String, Double> low_assign,
				HashMap<String, Double> high_assign, boolean use_low) {
			return use_low ? low_assign.get(_sVarName) : high_assign
					.get(_sVarName);
		}

		public void collectVars(HashSet<String> vars) {
			vars.add(_sVarName);
		}

		public Expr makeCanonical() {
			return new OperExpr(PROD, new DoubleExpr(1d), this);
		}

		@Override
		public String toString(boolean format) {
			return toString();
		}
	}

	public static String indent(int depth) {
		StringBuffer sb = new StringBuffer();
		for (int i = 0; i <= depth; i++)
			sb.append(STRING_TAB);
		return sb.toString();
	}

	// /////////////flush/////////////////////
	public void clearSpecialNodes() {
		_hsSpecialNodes.clear();
	}

	public void addSpecialNode(Integer n) {
		try {
			if (n == null)
				throw new Exception("addSpecialNode: null");
		} catch (Exception e) {
			System.out.println(e);
			e.printStackTrace();
			System.exit(1);
		}
		_hsSpecialNodes.add(n);
	}

	public void flushCaches() {
		//System.out.print("[FLUSHING CACHES... ");
		if (((double)RUNTIME.freeMemory() / 
				(double)RUNTIME.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			System.out.println("No need to flush caches.");
			return; // Still enough free mem to exceed minimum requirements
		}
		// Can always clear these
		_hmReduceCache.clear();
		_hmReduceLPCache.clear();
		_hmReduceLeafOpCache.clear();
		_hmApplyCache.clear();
		_hmINode2Vars.clear();
		_hmLinearDecisions.clear();
		_hmReduceAnnotateCache.clear();

		// Set up temporary alternates to these HashMaps
		_hmNode2IntNew = new HashMap<XADDNode, Integer>();
		_hmInt2NodeNew = new HashMap<Integer, XADDNode>();

		// Copy over 'special' nodes then set new maps
		//System.out.println(_hsSpecialNodes);
		for (Integer n : _hsSpecialNodes) {
			copyInNewCacheNode(n);
		}
		_hmNode2Int = _hmNode2IntNew;
		_hmInt2Node = _hmInt2NodeNew;

		Runtime.getRuntime().gc();

	}

	private void copyInNewCacheNode(Integer id) {

		if (_hmInt2NodeNew.containsKey(id)) {
			return;
		}
		Object node = _hmInt2Node.get(id);
		if (node instanceof XADDINode) {
			Integer fh = ((XADDINode) node)._high;
			Integer fl = ((XADDINode) node)._low;
			_hmInt2NodeNew.put(id, (XADDINode) node);
			_hmNode2IntNew.put((XADDINode) node, id);
			copyInNewCacheNode(((XADDINode) node)._high);
			copyInNewCacheNode(((XADDINode) node)._low);
		} else if (node instanceof XADDTNode) {
			_hmInt2NodeNew.put(id, (XADDTNode) node);
			_hmNode2IntNew.put((XADDTNode) node, id);

		}
	}

}