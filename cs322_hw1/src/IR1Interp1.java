// 
// A starting version of IR1 interpreter. (For CS322 W15 Assignment 1)
// Student: Jong Seong Lee
// Date: 01/23/15
//
import java.util.*;
import java.io.*;
import ir1.*;

public class IR1Interp1 {

  static class IntException extends Exception {
    public IntException(String msg) { super(msg); }
  }

  //-----------------------------------------------------------------
  // Value representation
  //-----------------------------------------------------------------
  //
  abstract static class Val {
	int asInt() throws Exception {
      throw new IntException("Integer value expected");
    }
    
    boolean asBool() throws Exception {
      throw new IntException("Boolean value expected");
    }
  }

  // Integer values
  //
  static class IntVal extends Val {
    int i;
    IntVal(int i) { this.i = i; }
    public String toString() { return "" + i; }
    int asInt() throws Exception { return this.i; }
  }

  // Boolean values
  //
  static class BoolVal extends Val {
    boolean b;
    BoolVal(boolean b) { this.b = b; }
    public String toString() { return "" + b; }
    boolean asBool() throws Exception { return this.b; }
  }

  // String values
  //
  static class StrVal extends Val {
    String s;
    StrVal(String s) { this.s = s; }
    public String toString() { return s; }
  }

  // A special "undefined" value
  //
  static class UndVal extends Val {
    public String toString() { return "UndVal"; }
  }

  //-----------------------------------------------------------------
  // Environment representation
  //-----------------------------------------------------------------
  //
  // Think of how to organize environments.
  // 
  // The following environments are shown in the lecture for use in 
  // an IR0 interpreter:
  //
  //   HashMap<String,Integer> labelMap;  // label table
  //   HashMap<Integer,Val> tempMap;	  // temp table
  //   HashMap<String,Val> varMap;	  // var table
  // 
  // For IR1, they need to be managed at per function level.
  // 

  // ... code needed ...
  static IR1.Src[] temp;
  static Stack<Env> envStack = new Stack<Env>();
  static Stack<VarEnv> varEnvStack = new Stack<VarEnv>();
  
  static class VarEnv {
	HashMap<String,Val> varMap = null;	  		// var table  
  
	VarEnv() {
		varMap = new HashMap<String,Val>();
	}
	public void extendVar(String key, Val value) throws Exception{
		varMap.put(key, value);
	}
	public Val lookupVar(String key) throws Exception {
		if(varMap.containsKey(key))
				return varMap.get(key);
		throw new Exception("Variable " + key + " not defined!");
	}
  }
  
  static class Env {
    HashMap<String,Integer> labelMap = null;  	// label table
	HashMap<Integer,Val> tempMap = null;	  	// temp table
	
	Env() {
		labelMap = new HashMap<String,Integer>();
		tempMap = new HashMap<Integer,Val>();	
	}
	
	public void extendLabel(String key, int value) throws Exception {
		labelMap.put(key, value);
	}
	public void extendTemp(int key, Val value) throws Exception {
		tempMap.put(key, value);
	}
	
	public int lookupLabel(String key) throws Exception {
		if(labelMap.containsKey(key))
				return labelMap.get(key);
		throw new Exception("Label " + key + " not defined!");
	}
	public Val lookupTemp(int key) throws Exception {
		if(tempMap.containsKey(key))
				return tempMap.get(key);
		throw new Exception("Temp " + key + " not defined!");
	}
  }
  
  //-----------------------------------------------------------------
  // Global variables and constants
  //-----------------------------------------------------------------
  //
  // These variables and constants are for your reference only.
  // You may decide to use all of them, some of these, or not at all.
  //

  // Function lookup table
  // - maps function names to their AST nodes
  //
  static HashMap<String, IR1.Func> funcMap; 	

  // Heap memory
  // - for handling 'malloc'ed data
  // - you need to define alloc and access methods for it
  //
  static ArrayList<Val> heap;		

  // Return value
  // - for passing return value from callee to caller
  //
  static Val retVal;

  // Execution status
  // - tells whether to continue with the nest inst, to jump to
  //   a new target inst, or to return to the caller
  //
  static final int CONTINUE = 0;
  static final int RETURN = -1;	

  //-----------------------------------------------------------------
  // The main method
  //-----------------------------------------------------------------
  //
  // 1. Open an IR1 program file. 
  // 2. Call the IR1 AST parser to read in the program and 
  //    convert it to an AST (rooted at an IR1.Program node).
  // 3. Invoke the interpretation process on the root node.
  //
  public static void main(String [] args) throws Exception {
    if (args.length == 1) {
      FileInputStream stream = new FileInputStream(args[0]);
      IR1.Program p = new ir1Parser(stream).Program();
      stream.close();
      execute(p);
    } else {
      System.out.println("You must provide an input file name.");
    }
  }

  //-----------------------------------------------------------------
  // Top-level IR nodes
  //-----------------------------------------------------------------
  //

  // Program ---
  //  Func[] funcs;
  //
  // 1. Establish the function lookup map
  // 2. Lookup 'main' in funcMap, and 
  // 3. start interpreting from main's AST node
  //
  public static void execute(IR1.Program n) throws Exception { 
    funcMap = new HashMap<String,IR1.Func>();
    heap = new ArrayList<Val>();
    retVal = new UndVal();
    for (IR1.Func f: n.funcs)
      funcMap.put(f.name, f);
    execute(funcMap.get("main"));
  }

  // Func ---
  //  String name;
  //  Var[] params;
  //  Var[] locals;
  //  Inst[] code;
  //
  // 1. Collect label decls information and store them in
  //    a label-lookup table for later use.
  // 2. Execute the fetch-and-execute loop.
  //
  static void execute(IR1.Func n) throws Exception { 
	
	VarEnv varEnv = varEnvStack.push(new VarEnv());  
	  
	for (String s: n.locals)
		varEnv.extendVar(s, null);
    
	Env env = envStack.push(new Env());
	
	for (int i = 0; i < n.code.length; i++) {
      if ((n.code[i] instanceof IR1.LabelDec)) {
        env.extendLabel(((IR1.LabelDec)n.code[i]).name, Integer.valueOf(i));
      }
    }
    
	// The fetch-and-execute loop
    int idx = 0;
    while (idx < n.code.length) {
      int next = execute(n.code[idx]);
      if (next == CONTINUE)
		idx++; 
      else if (next == RETURN)
        break;
      else
	idx = next;
    }
	
	envStack.pop(); 
  }

  // Dispatch execution to an individual Inst node.
  //
  static int execute(IR1.Inst n) throws Exception {
    if (n instanceof IR1.Binop)    return execute((IR1.Binop) n);
    if (n instanceof IR1.Unop) 	   return execute((IR1.Unop) n);
    if (n instanceof IR1.Move) 	   return execute((IR1.Move) n);
    if (n instanceof IR1.Load) 	   return execute((IR1.Load) n);
    if (n instanceof IR1.Store)    return execute((IR1.Store) n);
    if (n instanceof IR1.Jump) 	   return execute((IR1.Jump) n);
    if (n instanceof IR1.CJump)    return execute((IR1.CJump) n);
    if (n instanceof IR1.Call)     return execute((IR1.Call) n);
    if (n instanceof IR1.Return)   return execute((IR1.Return) n);
    if (n instanceof IR1.LabelDec) return CONTINUE;
    throw new IntException("Unknown Inst: " + n);
  }
  
  static void assign(IR1.Dest dst, Val val) throws Exception
  {
    if ((dst instanceof IR1.Temp)) {
      envStack.peek().extendTemp(Integer.valueOf(((IR1.Temp)dst).num), val);
    } else if ((dst instanceof IR1.Id)) {
      if (varEnvStack.empty())
    	  varEnvStack.push(new VarEnv());
      varEnvStack.peek().extendVar(((IR1.Id)dst).name, val);
    }
  }

  //-----------------------------------------------------------------
  // Execution routines for individual Inst nodes
  //-----------------------------------------------------------------
  //
  // - Each execute() routine returns CONTINUE, RETURN, or a new idx 
  //   (target of jump).
  //

  // Binop ---
  //  BOP op;
  //  Dest dst;
  //  Src src1, src2;
  //
  static int execute(IR1.Binop n) throws Exception {
	Val lval = execute(n.src1);
    Val rval = execute(n.src2);
    Val res = null;
    if (((lval instanceof IntVal)) && ((rval instanceof IntVal)))
    {

      int l = lval.asInt();
      int r = rval.asInt();
      
      switch ((IR1.AOP)n.op)
      {
      case ADD: 
        res = new IntVal(l + r); break;
      case SUB: 
        res = new IntVal(l - r); break;
      case MUL: 
        res = new IntVal(l * r); break;
      case DIV: 
        res = new IntVal(l / r); break;
      default: 
        throw new IntException("Arithetic Operator expected in Binop: " + n.op);
      }
    }
    else if (((lval instanceof BoolVal)) && ((rval instanceof BoolVal)))
    {
      boolean l = lval.asBool();
      boolean r = rval.asBool();
      switch ((IR1.AOP)n.op)
      {
      case AND: 
        res = new BoolVal((l) && (r)); break;
      case OR: 
        res = new BoolVal((l) || (r)); break;
      default: 
        throw new IntException("ArithOP expected in Binop: " + n.op);
      }
    }
    else
    {
      throw new IntException("Bad operands in Binop: " + n);
    }
    assign(n.dst, res);
    return CONTINUE;  
  }

  // Unop ---
  //  UOP op;
  //  Dest dst;
  //  Src src;
  //
  static int execute(IR1.Unop n) throws Exception {
	Val val = execute(n.src);
    Val res = null;
    if (n.op == IR1.UOP.NEG)
      res = new IntVal(-((IntVal) val).i);
    else if (n.op == IR1.UOP.NOT)
      res = new BoolVal(!((BoolVal) val).b);
    else
      throw new IntException("Wrong operator in Unop instruction: " + n.op);

    assign(n.dst, res);
    return CONTINUE;  
  }

  // Move ---
  //  Dest dst;
  //  Src src;
  //
  static int execute(IR1.Move n) throws Exception {

	Val val = execute(n.src);
    assign(n.dst, val);
	return CONTINUE;
  }

  // Load ---  
  //  Dest dst;
  //  Addr addr;
  //
  static int execute(IR1.Load n) throws Exception {
	int loc = execute(n.addr);
    Val val = (Val)heap.get(loc);
    if (val == null) {
      throw new IntException("Can't find a value at location " + loc);
    }
    assign(n.dst, val);
	return CONTINUE;
  }

  // Store ---  
  //  Addr addr;
  //  Src src;
  //
  static int execute(IR1.Store n) throws Exception {
	Val val = execute(n.src);
    int loc = execute(n.addr);
    heap.set(loc, val);
	return CONTINUE;
  }

  // CJump ---
  //  ROP op;
  //  Src src1, src2;
  //  Label lab;
  //
  static int execute(IR1.CJump n) throws Exception {
	boolean cond;
	Val lval = execute(n.src1);
    Val rval = execute(n.src2);
    
    if (((lval instanceof IntVal)) && ((rval instanceof IntVal)))
    {
      int l = lval.asInt();
      int r = rval.asInt();
      switch ((IR1.ROP)n.op)
      {
      case EQ: 
        cond = l == r; break;
      case NE: 
        cond = l != r; break;
      case LT: 
        cond = l < r; break;
      case LE: 
        cond = l <= r; break;
      case GT: 
        cond = l > r; break;
      case GE: 
        cond = l >= r; break;
      default: 
        throw new IntException("Wrong op in CJump: " + n.op);
      }
    }
    else
    { 
      if (((lval instanceof BoolVal)) && ((rval instanceof BoolVal)))
      {
        boolean l = lval.asBool();
        boolean r = rval.asBool();
        switch (n.op)
        {
        case EQ: 
          cond = l == r; break;
        case NE: 
          cond = l != r; break;
        default: 
          throw new IntException("Wrong op in CJump: " + n.op);
        }
      }
      else
      {
        throw new IntException("Error in CJump: " + n);
      }
    }
    
    if (cond) {
      return ((Integer)envStack.peek().lookupLabel(n.lab.name)).intValue();
    }
	return CONTINUE;
  }	

  // Jump ---
  //  Label lab;
  //
  static int execute(IR1.Jump n) throws Exception {
	return ((Integer)envStack.peek().lookupLabel(n.lab.name)).intValue();
  }	

  // Call ---
  //  String name;
  //  Src[] args;
  //  Dest rdst;
  //
  static int execute(IR1.Call n) throws Exception {
	VarEnv varEnv = varEnvStack.peek();
	
	if ((n.name.equals("printInt")) || (n.name.equals("printBool")))
    {
      assert ((n.args != null) && (n.args.length == 1));
      Val val = execute(n.args[0]);
      System.out.println(val);
    }
    else if (n.name.equals("printStr"))
    {
      if ((n.args == null) || (n.args.length == 0))
      {
        System.out.println();
      }
      else
      {
        Val val = execute(n.args[0]);
        System.out.println(val);
      }
    }
    else if (n.name.equals("malloc"))
    {
      assert (n.args != null);
      int size = execute(n.args[0]).asInt();
      int loc = storageAllocation(size);
      assign(n.rdst, new IntVal(loc));
    }
    else
    {
      IR1.Func func = (IR1.Func)funcMap.get(n.name);
      
      for (int i = 0; i < func.params.length; i++)
      {
        String pname = func.params[i];
        Val argval = execute(n.args[i]);
        
        varEnv.extendVar(pname, argval);
      }
      execute(func);
      assign(n.rdst, retVal);
    }
    return CONTINUE;
  }

  static int storageAllocation(int size)
  {
    int loc = heap.size();
    for (int i = 0; i < size; i++) {
      heap.add(new UndVal());
    }
    return loc;
  }
  
  // Return ---  
  //  Src val;
  //
  static int execute(IR1.Return n) throws Exception {
	if (n.val != null) {
      retVal = execute(n.val);
    }
    varEnvStack.pop();
    return RETURN;
  }

  //-----------------------------------------------------------------
  // Evaluatation routines for address
  //-----------------------------------------------------------------
  //
  // - Returns an integer (representing index to the heap memory).
  //
  // Address ---
  //  Src base;  
  //  int offset;
  //
  static int execute(IR1.Addr n) throws Exception {
	int loc = execute(n.base).asInt();
    return loc + n.offset;
  }

  //-----------------------------------------------------------------
  // Evaluatation routines for operands
  //-----------------------------------------------------------------
  //
  // - Each evaluate() routine returns a Val object.
  //
  static Val execute(IR1.Src n) throws Exception {
	Val val = null;
    if ((n instanceof IR1.Temp)) {
      val = execute((IR1.Temp)n);
    }
    if ((n instanceof IR1.Id)) {
      val = execute((IR1.Id)n);
    }
    if ((n instanceof IR1.IntLit)) {
      val = execute((IR1.IntLit)n);
    }
    if ((n instanceof IR1.BoolLit)) {
      val = execute((IR1.BoolLit)n);
    }
    if ((n instanceof IR1.StrLit)) {
      return execute((IR1.StrLit)n);
    }
    if (val == null) {
      throw new IntException("Src '" + n + "' has no value");
    } 
    return val;
  }

  static Val execute(IR1.Temp n) throws Exception
  {
	return (Val)envStack.peek().lookupTemp(Integer.valueOf(n.num));
  }
  
  static Val execute(IR1.Id n) throws Exception
  {
	if (varEnvStack.empty())
  	  varEnvStack.push(new VarEnv());
    return (Val)varEnvStack.peek().lookupVar(n.name);
  }
  
  static IntVal execute(IR1.IntLit n) throws Exception
  {
    return new IntVal(n.i);
  }
  
  static BoolVal execute(IR1.BoolLit n) throws Exception
  {
    return new BoolVal(n.b);
  }
  
  static StrVal execute(IR1.StrLit n) throws Exception
  {
    return new StrVal(n.s);
  }
  
  static Val evaluate(IR1.Dest n) throws Exception {
    Val val = null;
    if ((n instanceof IR1.Temp)) {
      val = execute((IR1.Temp)n);
    }
    if ((n instanceof IR1.Id)) {
      val = execute((IR1.Id)n);
    }
    
    if (val == null) {
      throw new IntException("Dest '" + n + "' has no value!");
    } 
    return val;
  }

}
