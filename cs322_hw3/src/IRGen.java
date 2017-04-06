// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
// 
// IR code generator for miniJava's AST.
//
// Student: Jong Seong Lee
// Date: 03/01/15
//

import java.util.*;
import java.io.*;
import ast.*;
import ast.Ast.VarDecl;
import ir.*;
import ir.IR.Type;

public class IRGen {

  static class GenException extends Exception {
    public GenException(String msg) { super(msg); }
  }

  //------------------------------------------------------------------------------
  // ClassInfo
  //----------
  // For keeping all useful information about a class declaration for use 
  // in the codegen.
  //
  static class ClassInfo {
    Ast.ClassDecl cdecl; 	// classDecl AST
    ClassInfo parent; 		// pointer to parent
    List<String> vtable; 	// method-label table        
    List<Ast.VarDecl> fdecls;   // field decls (incl. inherited ones)
    List<Integer> offsets;      // field offsets
    int objSize; 		// object size
    //boolean containsMain = false;

    // Constructor -- clone a parent's record
    //
    ClassInfo(Ast.ClassDecl cdecl, ClassInfo parent) {
      this.cdecl = cdecl;
      this.parent = parent;
      this.vtable = new ArrayList<String>(parent.vtable);
      this.fdecls = new ArrayList<Ast.VarDecl>(parent.fdecls); 
      this.offsets = new ArrayList<Integer>(parent.offsets); 
      this.objSize = parent.objSize;
    }      

    // Constructor -- create a new record
    //
    ClassInfo(Ast.ClassDecl cdecl) {
      this.cdecl = cdecl;
      this.parent = null;
      this.vtable = new ArrayList<String>();
      this.fdecls = new ArrayList<Ast.VarDecl>(); 
      this.offsets = new ArrayList<Integer>(); 
      this.objSize = IR.Type.PTR.size; 	// reserve space for ptr to class
    }      

    // Utility Routines
    // ----------------
    // For accessing information stored in class information record
    //

    // Return the name of this class 
    //
    String className() { return cdecl.nm; }

    // Find method's base class record
    //
    ClassInfo methodBaseClass(String mname) throws Exception {
      for (Ast.MethodDecl mdecl: cdecl.mthds)
	if (mdecl.nm.equals(mname)) 
	  return this;
      if (parent != null)
        return parent.methodBaseClass(mname);
      throw new GenException("Can't find base class for method " + mname);
    }	

    // Find method's return type
    //
    Ast.Type methodType(String mname) throws Exception {
      for (Ast.MethodDecl mdecl: cdecl.mthds)
	if (mdecl.nm.equals(mname))
	  return mdecl.t;
      if (parent != null)
        return parent.methodType(mname);
      throw new GenException("Can't find MethodDecl for method " + mname);
    }

    // Return method's vtable offset
    //
    int methodOffset(String mname) {
      return vtable.indexOf(mname) * IR.Type.PTR.size;
    }

    // Find field variable's type
    //
    Ast.Type fieldType(String fname) throws Exception {
      for (Ast.VarDecl fdecl: cdecl.flds) { // so classdecl's flds matters
		if (fdecl.nm.equals(fname))
		  return fdecl.t;
      }
      if (parent != null)
        return parent.fieldType(fname);
      throw new GenException("Can't find VarDecl for field " + fname);
    }

    // Return field variable's offset
    //
    int fieldOffset(String fname) throws Exception {
      for (int i=fdecls.size()-1; i>=0; i--) {
		if (fdecls.get(i).nm.equals(fname))
		  return offsets.get(i);
      }
	      throw new GenException("Can't find offset for field " + fname);
    }

    public String toString() {
      return "ClassInfo: " + " " + cdecl + " " + parent + " "
		+ " " + vtable + " " + offsets + " " + objSize;
      }
  }

  //------------------------------------------------------------------------------
  // Other Supporting Data Structures
  //---------------------------------

  // CodePack
  // --------
  // For returning <type,src,code> tuple from gen() routines
  //
  static class CodePack {
    IR.Type type;
    IR.Src src;
    List<IR.Inst> code;
    CodePack(IR.Type type, IR.Src src, List<IR.Inst> code) { 
      this.type=type; this.src=src; this.code=code; 
    }
    CodePack(IR.Type type, IR.Src src) { 
      this.type=type; this.src=src; code=new ArrayList<IR.Inst>(); 
    }
  }

  // AddrPack
  // --------
  // For returning <type,addr,code> tuple from genAddr routines
  //
  static class AddrPack {
    IR.Type type;
    IR.Addr addr;
    List<IR.Inst> code;
    AddrPack(IR.Type type, IR.Addr addr, List<IR.Inst> code) { 
      this.type=type; this.addr=addr; this.code=code; 
    }
  }

  // Env
  // ---
  // For keeping track of local variables and parameters and for finding 
  // their types.
  //
  private static class Env extends HashMap<String,Ast.Type> {}


  //------------------------------------------------------------------------------
  // Global Variables
  // ----------------
  //

  // Env for ClassInfo records
  private static HashMap<String,ClassInfo> classEnv = new HashMap<String,ClassInfo>();

  private static Env globalVars = new Env();
  private static boolean objExist = false;
  private static HashMap<String,String> objToClass = new HashMap<String,String>();
  
  // IR code representation of the current object
  private static IR.Src thisObj = new IR.Id("obj");


  //------------------------------------------------------------------------------
  // Utility routines
  // ----------------
  //

  // Sort ClassDecls based on parent-children relationship.
  //
  private static Ast.ClassDecl[] topoSort(Ast.ClassDecl[] classes) {
    List<Ast.ClassDecl> cl = new ArrayList<Ast.ClassDecl>();
    Vector<String> done = new Vector<String>();
    int cnt = classes.length;
    while (cnt > 0) {
      for (Ast.ClassDecl cd: classes)
	if (!done.contains(cd.nm)
	    && ((cd.pnm == null) || done.contains(cd.pnm))) {
	  cl.add(cd);
	  done.add(cd.nm);
	  cnt--;
	} 
    }
    return cl.toArray(new Ast.ClassDecl[0]);
  }

  // Return an object's base classInfo.
  //  (The parameter n is known to represent an object when call
  //  is made.)
  //
  private static ClassInfo getClassInfo(Ast.Exp n, ClassInfo cinfo, 
					Env env) throws Exception {
	Ast.Type typ = null;
    if (n instanceof Ast.This)
      return cinfo;
    if (n instanceof Ast.Id) {
      typ = env.get(((Ast.Id) n).nm);
      if (typ == null) // id is a field with a missing "this" pointer
    	  typ = cinfo.fieldType(((Ast.Id) n).nm);
    } else if (n instanceof Ast.Field) {
      ClassInfo base = getClassInfo(((Ast.Field) n).obj, cinfo, env);
      typ = base.fieldType(((Ast.Field) n).nm);
    } else {
      throw new GenException("Unexpected obj epxression " + n);  
    }
    if (!(typ instanceof Ast.ObjType))
      throw new GenException("Expects an ObjType, got " + typ);  
    return classEnv.get(((Ast.ObjType) typ).nm);
  }	

  // Create ClassInfo record
  //
  // Codegen Guideline: 
  // 1. If parent exists, clone parent's record; otherwise create a new one
  // 2. Walk the MethodDecl list. If a method is not in the v-table, add it in;
  // 3. Compute offset values for field variables
  // 4. Decide object's size
  //
  private static ClassInfo createClassInfo(Ast.ClassDecl n) throws Exception {
	  
	  ClassInfo cinfo = (n.pnm != null) ?
        new ClassInfo(n, classEnv.get(n.pnm)) : new ClassInfo(n);
        
      for (Ast.MethodDecl m : n.mthds) {
		  if (!cinfo.vtable.contains(m.nm)) {
		      cinfo.vtable.add(m.nm);
		  }
      }
      
	  int offsetCounter = cinfo.objSize;
	  for (Ast.VarDecl v : n.flds) {
		  if(!cinfo.fdecls.contains(v)) {
			  cinfo.fdecls.add(v);
		  }
	      cinfo.offsets.add(offsetCounter);
	      offsetCounter += gen(v.t).size;
	  }
	  
	  cinfo.objSize = offsetCounter;
	  return cinfo;
  }


  //------------------------------------------------------------------------------
  // The Main Routine
  //-----------------
  //
  public static void main(String [] args) throws Exception {
    if (args.length == 1) {
      FileInputStream stream = new FileInputStream(args[0]);
      Ast.Program p = new astParser(stream).Program();
      stream.close();
      IR.Program ir = gen(p);
      System.out.print(ir.toString());
    } else {
      System.out.println("You must provide an input file name.");
    }
  }

  //------------------------------------------------------------------------------
  // Codegen Routines for Individual AST Nodes
  //------------------------------------------

  // Program ---
  // ClassDecl[] classes;
  //
  // Three passes over a program:
  //  0. topo-sort class decls
  //  1. create ClassInfo records 
  //  2. generate IR code
  //     2.1 generate list of static data (i.e. class descriptors)
  //     2.2 generate list of functions
  //
  public static IR.Program gen(Ast.Program n) throws Exception {
    Ast.ClassDecl[] classes = topoSort(n.classes);
    
    ClassInfo cinfo;
    for (Ast.ClassDecl c: classes) {
      cinfo = createClassInfo(c);
      classEnv.put(c.nm, cinfo);
    }
    List<IR.Data> allData = new ArrayList<IR.Data>();
    List<IR.Func> allFuncs = new ArrayList<IR.Func>();
    for (Ast.ClassDecl c: classes) {
      cinfo = classEnv.get(c.nm);
      IR.Data data = genData(c, cinfo);
      List<IR.Func> funcs = gen(c, cinfo);
      if (data != null)
	allData.add(data);
      allFuncs.addAll(funcs);
    }
    return new IR.Program(allData, allFuncs);
  }

  // ClassDecl ---
  // String nm, pnm;
  // VarDecl[] flds;
  // MethodDecl[] mthds;
  //

  // 1. Generate static data
  //
  // Codegen Guideline: 
  //   1.1 For each method in class's vtable, construct a global label of form
  //       "<base class name>_<method name>" and save it in an IR.Global node
  //   1.2 Assemble the list of IR.Global nodes into an IR.Data node with a
  //       global label "class_<class name>"
  //
  static IR.Data genData(Ast.ClassDecl n, ClassInfo cinfo) throws Exception {
	  List<IR.Global> globalList = new ArrayList<IR.Global>();
	  List<String> methodList = new ArrayList<String>();
	  int size = 0;
	  
	  for(Ast.MethodDecl m: n.mthds) {
		  String parentClassName = "";
		  
		  ClassInfo ciBase = classEnv.get(n.pnm);
		  
		  if(n.pnm != null && ciBase.vtable.size() > 0 && !cinfo.vtable.get(0).toString().equals(m.nm)) {
			  parentClassName = n.pnm + "_" + cinfo.vtable.get(0).toString() + ", _";
			  size += 8;
			  methodList.add(cinfo.vtable.get(0).toString());
		  }
		  
		  String methodName = m.nm;
		  methodList.add(m.nm);
		  if(!methodName.equals("main")) {
			  
			  methodName = n.nm + "_" + methodName;
		  }
		  
		  if(n.pnm != null) {
			  for(String s : ciBase.vtable) {
				  if(!s.equals(m.nm) && !methodList.contains(s)) {
					  methodName = methodName + ", _" + cinfo.parent.className() + "_" + s;
					  size += 8;
					  methodList.add(s);
				  }
			  }  
		  }
		  
		  globalList.add(new IR.Global(parentClassName + methodName));
		  size += 8;
	  }
	  
	  return new IR.Data(new IR.Global("class_" + n.nm), size, globalList);
  }

  // 2. Generate code
  //
  // Codegen Guideline: 
  //   Straightforward -- generate a IR.Func for each mthdDecl.
  //
  static List<IR.Func> gen(Ast.ClassDecl n, ClassInfo cinfo) throws Exception {
	  List<IR.Func> retList = new ArrayList<IR.Func>(); 
	  
	  for (Ast.VarDecl f : n.flds) {
		  globalVars.put(f.nm, f.t);
		  objToClass.put(f.nm, cinfo.className());
		  objExist = true;
	  }
	  
	  for (Ast.MethodDecl m : n.mthds) {
		  retList.add(gen(m, cinfo));
	  }
	  return retList;
  }

  // MethodDecl ---
  // Type t;
  // String nm;
  // Param[] params;
  // VarDecl[] vars;
  // Stmt[] stmts;
  //
  // Codegen Guideline: 
  // 1. Construct a global label of form "<base class name>_<method name>"
  // 2. Add "obj" into the params list as the 0th item
  // (Skip these two steps if method is "main".)
  // 3. Create an Env() containing all params and all local vars 
  // 4. Generate IR code for all statements
  // 5. Return an IR.Func with the above
  //
  static IR.Func gen(Ast.MethodDecl n, ClassInfo cinfo) throws Exception {
	  //    ... need code
	  List<IR.Inst> instList = new ArrayList<IR.Inst>(); 
	  List<String> paramList = new ArrayList<String>();
      List<String> varList = new ArrayList<String>();
      IR.Temp.reset();
      
      IR.Global label;
      if (!n.nm.equals("main")) {
          label = new IR.Global(cinfo.className() + "_" + n.nm);
          paramList.add("obj");
      } else {
          label = new IR.Global("main");
      }

      Env newEnv = new Env();
      for (Ast.Param p : n.params) {
    	  
          newEnv.put(p.nm, p.t);
          paramList.add(p.nm);
      }

      for (Ast.VarDecl v : n.vars) {
          newEnv.put(v.nm, v.t);
          varList.add(v.nm);
          List<IR.Inst> insTemp = gen(v, cinfo, newEnv);
          if (insTemp != null)
              instList.addAll(insTemp);
      }

      for (Ast.Stmt s : n.stmts) {
          instList.addAll(gen(s, cinfo, newEnv));
      }

      if (cinfo.methodType(n.nm) == null) {
          instList.add(new IR.Return());
      }

      return new IR.Func(label.name, paramList, varList, instList);
  } 

  // VarDecl ---
  // Type t;
  // String nm;
  // Exp init;
  //
  // Codegen Guideline: 
  // 1. If init exp exists, generate IR code for it and assign result to var
  // 2. Return generated code (or null if none)
  //
  private static List<IR.Inst> gen(Ast.VarDecl n, ClassInfo cinfo, Env env) throws Exception {
	  if(n.init != null) {
		  List<IR.Inst> instList = new ArrayList<IR.Inst>();
		  CodePack cp = gen(n.init, cinfo, env);
		  IR.Move move = new IR.Move(new IR.Id(n.nm), cp.src);
		  instList.addAll(cp.code);
		  instList.add(move);
		  
		  if(n.init instanceof Ast.NewObj) {
			  objToClass.put(n.nm, ((Ast.NewObj)n.init).nm);  
		  }
		  return instList;
	  } else {
		  return null;
	  }
  }

  // STATEMENTS

  // Dispatch a generic call to a specific Stmt routine
  // 
  static List<IR.Inst> gen(Ast.Stmt n, ClassInfo cinfo, Env env) throws Exception {
    if (n instanceof Ast.Block)    return gen((Ast.Block) n, cinfo, env);
    if (n instanceof Ast.Assign)   return gen((Ast.Assign) n, cinfo, env);
    if (n instanceof Ast.CallStmt) return gen((Ast.CallStmt) n, cinfo, env);
    if (n instanceof Ast.If)       return gen((Ast.If) n, cinfo, env);
    if (n instanceof Ast.While)    return gen((Ast.While) n, cinfo, env);
    if (n instanceof Ast.Print)    return gen((Ast.Print) n, cinfo, env);
    if (n instanceof Ast.Return)   return gen((Ast.Return) n, cinfo, env);
    throw new GenException("Illegal Ast Stmt: " + n);
  }

  // Block ---
  // Stmt[] stmts;
  //
  static List<IR.Inst> gen(Ast.Block n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  
	  for(Ast.Stmt s : n.stmts) {
		  instList.addAll(gen(s, cinfo, env));
	  }
		  
	  return instList;
  }

  // Assign ---
  // Exp lhs, rhs;
  //
  // Codegen Guideline: 
  // 1. call gen() on rhs
  // 2. if lhs is ID, check against Env to see if it's a local var or a param;
  //    if yes, generate an IR.Move instruction
  // 3. otherwise, call genAddr() on lhs, and generate an IR.Store instruction
  //
  static List<IR.Inst> gen(Ast.Assign n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  CodePack cp = gen(n.rhs, cinfo, env);
	  instList.addAll(cp.code);
	  
	  if(n.lhs instanceof Ast.Id) {
		  
		  if(env.containsKey(((Ast.Id)n.lhs).nm)) {
			  IR.Dest lhs = new IR.Id(((Ast.Id)n.lhs).nm);
			  instList.add(new IR.Move(lhs, cp.src));
			  instList.addAll(cp.code);
		  } else {
			  IR.Src source = cp.src;
			  if(cinfo.className().equals(objToClass.get(((Ast.Id)n.lhs).nm))
					  && n.rhs instanceof Ast.Id
					  && cinfo.parent.className().equals(objToClass.get(((Ast.Id)n.rhs).nm))) {
				  
				  ClassInfo ci = classEnv.get(objToClass.get(((Ast.Id)n.rhs).nm));
				  IR.Type type = gen(ci.fieldType(((Ast.Id)n.rhs).nm));
				  int offsetSize = ci.fieldOffset(((Ast.Id)n.rhs).nm);
				  
				  IR.Temp temp = new IR.Temp();
				  Ast.Field field = new Ast.Field(new Ast.This(), ((Ast.Id)n.lhs).nm);
				  AddrPack ap = genAddr(field, cinfo, env);
				  
				  instList.add(new IR.Load(type, temp, new IR.Addr(thisObj, offsetSize)));
				  source = temp;
			  }
				  
			  Ast.Field field = new Ast.Field(new Ast.This(), ((Ast.Id)n.lhs).nm);
			  AddrPack ap = genAddr(field, cinfo, env);
			  instList.addAll(cp.code);
			  ClassInfo ciCheck = classEnv.get(objToClass.get(((Ast.Id)n.lhs).nm));
			  IR.Type type = gen(ciCheck.fieldType(((Ast.Id)n.lhs).nm));
			  
			  if(type == null && n.lhs instanceof Ast.Id) {
				  ClassInfo ci = classEnv.get(objToClass.get(((Ast.Id)n.lhs).nm));
				  type = gen(ci.fieldType(field.nm));
        		
			  }
			  instList.add(new IR.Store(type, ap.addr, source));
		  }
	  } else {
		  AddrPack ap = genAddr((Ast.Field)n.lhs, cinfo, env);
		  instList.addAll(ap.code);
		  instList.add(new IR.Store(cp.type, ap.addr, cp.src));
		  
		  Ast.Type type = null;
		  if(cp.type == IR.Type.INT){
			  type = Ast.IntType;
		  } else if (cp.type == IR.Type.BOOL) { 
			  type = Ast.BoolType;
		  }
		  
		  if(n.lhs instanceof Ast.Field && (!globalVars.containsKey(((Ast.Field)(n.lhs)).nm))) {
			  globalVars.put(((Ast.Field)n.lhs).nm, type);
		  }
	  }
	  return instList;
  }

  // CallStmt ---
  // Exp obj; 
  // String nm;
  // Exp[] args;
  //
  //
  static List<IR.Inst> gen(Ast.CallStmt n, ClassInfo cinfo, Env env) throws Exception {
    if (n.obj != null) {
      CodePack p = handleCall(n.obj, n.nm, n.args, cinfo, env, false);
      return p.code;
    }
    throw new GenException("In CallStmt, obj is null " + n);  
  }

  // handleCall
  // ----------
  // Common routine for Call and CallStmt nodes
  //
  // Codegen Guideline: 
  // 1. Invoke gen() on obj, which returns obj's storage address (and type and code)
  // 2. Call getClassInfo() on obj to get base ClassInfo
  // 3. Access the base class's ClassInfo rec to get the method's offset in vtable 
  // 4. Add obj's as the 0th argument to the args list
  // 5. Generate an IR.Load to get the class descriptor from obj's storage
  // 6. Generate another IR.Load to get the method's global label
  // 7. If retFlag is set, prepare a temp for receiving return value; also figure
  //    out return value's type (through method's decl in ClassInfo rec)
  // 8. Generate an indirect call with the global label
  //
  static CodePack handleCall(Ast.Exp obj, String name, Ast.Exp[] args, 
			     ClassInfo cinfo, Env env, boolean retFlag) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
      List<IR.Src> srcList = new ArrayList<IR.Src>();
      
      CodePack cp = gen(obj, cinfo, env);
      ClassInfo ciBase = getClassInfo(obj, cinfo, env);
      int offset = ciBase.methodOffset(name);
      
      srcList.add(cp.src);
      instList.addAll(cp.code);
      
      IR.Temp temp = new IR.Temp();
      IR.Load load = new IR.Load(IR.Type.PTR, temp, new IR.Addr(cp.src));
      instList.add(load);
      
      IR.Temp temp2 = new IR.Temp();
      IR.Load load2 = new IR.Load(IR.Type.PTR, temp2, new IR.Addr(temp, offset));
      instList.add(load2);
      
      IR.Temp temp3 = null;
      Ast.Type type = null;
      if(retFlag) {
    	  temp3 = new IR.Temp();
    	  type = ciBase.methodType(name);
      }
      
      for (Ast.Exp e : args) {
          CodePack cp2 = gen(e, cinfo, env);
          instList.addAll(cp2.code);
          srcList.add(cp2.src);
      }

      instList.add(new IR.Call(temp2, true, srcList, temp3));

      return new CodePack(gen(type), temp3, instList);
  }

  // If ---
  // Exp cond;
  // Stmt s1, s2;
  //
  // (See class notes.)
  //
  static List<IR.Inst> gen(Ast.If n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  IR.Label L1 = new IR.Label();
	  
	  CodePack cp = gen(n.cond, cinfo, env);
	  
	  IR.Src source = cp.src;
	  
	  if (n.cond instanceof Ast.Field) {
		  IR.Temp temp = new IR.Temp();
		  
		  Ast.Field field = new Ast.Field(((Ast.Field)n.cond).obj, ((Ast.Field)n.cond).nm);
		  
		  AddrPack ap = genAddr(field, cinfo, env);
    	  IR.Type typecheck = gen(globalVars.get(field.nm));
    	  IR.Load load = new IR.Load(typecheck, temp, ap.addr);
    	  instList.add(load);
    	  
    	  source = temp;
	  }
	  
	  instList.addAll(cp.code);
	  instList.add(new IR.CJump(IR.ROP.EQ, source, IR.FALSE, L1));
	  instList.addAll(gen(n.s1, cinfo, env));
	  
	  if(n.s2 == null) {
		  instList.add(new IR.LabelDec(L1));
	  } else {
		  IR.Label L2 = new IR.Label();
		  instList.add(new IR.Jump(L2));
		  instList.add(new IR.LabelDec(L1));
		  instList.addAll(gen(n.s2, cinfo, env));
		  instList.add(new IR.LabelDec(L2));
	  }  
	  return instList;
  }

  // While ---
  // Exp cond;
  // Stmt s;
  //
  // (See class notes.)
  //
  static List<IR.Inst> gen(Ast.While n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  IR.Label L1 = new IR.Label();
	  IR.Label L2 = new IR.Label();
	  
	  instList.add(new IR.LabelDec(L1));
	  CodePack cp = gen(n.cond, cinfo, env);
	  instList.addAll(cp.code);
	  instList.add(new IR.CJump(IR.ROP.EQ, cp.src, IR.FALSE, L2));
	  instList.addAll(gen(n.s, cinfo, env));
	  instList.add(new IR.Jump(L1));
	  instList.add(new IR.LabelDec(L2));
	  
	  return instList;
  }
  
  // Print ---
  // PrArg arg;
  //
  // Codegen Guideline: 
  // 1. If arg is null, generate an IR.Call to "printStr" with an empty string arg
  // 2. If arg is StrLit, generate an IR.Call to "printStr"
  // 3. Otherwise, generate IR code for arg, and use its type info
  //    to decide which of the two functions, "printInt" and "printBool",
  //    to call
  //
  static List<IR.Inst> gen(Ast.Print n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Src> srcList = new ArrayList<IR.Src>();
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  
	  if (n.arg == null) {
		  srcList.add(new IR.StrLit(""));
		  instList.add(new IR.Call(new IR.Global("printStr"), false, srcList));
	  } else if (n.arg instanceof Ast.StrLit) {
		  CodePack cp = gen((Ast.StrLit)n.arg);
		  srcList.add(cp.src);
		  instList.addAll(cp.code);
		  instList.add(new IR.Call(new IR.Global("printStr"), false, srcList));
	  } else {
		  CodePack cp = gen((Ast.Exp)(n.arg), cinfo, env);
		  
		  String globalName = null;
		  if (cp.type == IR.Type.INT) {
			  srcList.add(cp.src);
			  instList.addAll(cp.code);
              globalName = "printInt";
          } else if (cp.type == IR.Type.BOOL) {
        	  srcList.add(cp.src);
    		  instList.addAll(cp.code);
              globalName = "printBool";
          } else {
        	  
        	  if(n.arg instanceof Ast.Field) {
        		  IR.Temp temp = new IR.Temp();
        		  Ast.Field field = new Ast.Field(((Ast.Field)n.arg).obj, ((Ast.Field)n.arg).nm);
        		  AddrPack ap = genAddr(field, cinfo, env);
            	  IR.Type typecheck = gen(env.get(field.nm));
            	  
            	  if(typecheck == null) {
            		  typecheck = gen(globalVars.get(field.nm));
            	  }
	        	  if(typecheck == null) {
	        		  ClassInfo ci = classEnv.get(objToClass.get(((Ast.Field)n.arg).obj.toString()));
	        		  typecheck = gen(ci.fieldType(field.nm));
	        	  }
	        	  IR.Load load = new IR.Load(typecheck, temp, ap.addr); // wrong
            	  instList.add(load);
            	 
            	  if (typecheck == IR.Type.INT) {
                      globalName = "printInt";
                  } else if (typecheck == IR.Type.BOOL) {
                      globalName = "printBool";
                  } 
            	  
            	  srcList.add(temp);
        	  } else {
        		  
        		  if (objExist) {
		    		  IR.Temp temp = new IR.Temp();
		    		  
		    		  Ast.Field field = new Ast.Field(new Ast.This(), ((Ast.Id)n.arg).nm);
		    		  
		    		  AddrPack ap = genAddr(field, cinfo, env);
		    		  
		    		  IR.Type typecheck = gen(env.get(field.nm));
		        	  
		        	  if(typecheck == null) {
		        		  typecheck = gen(globalVars.get(field.nm));
		        	  }
		        	  
		        	  IR.Load load = new IR.Load(typecheck, temp, ap.addr); // wrong
		        	  instList.add(load);
		        	  
		        	  
		        	  if (typecheck == IR.Type.INT) {
		                  globalName = "printInt";
		              } else if (typecheck == IR.Type.BOOL) {
		                  globalName = "printBool";
		              } 
		        	  
		        	  srcList.add(temp);
        		  } else {
        			  IR.Type type = gen(env.get(((Ast.Id)n.arg).nm));
            		  
            		  if(type == null) {
            			  type = gen(globalVars.get(((Ast.Id)n.arg).nm));
            		  }
            		  
            		  if (type == IR.Type.INT) {
            			  srcList.add(cp.src);
            			  instList.addAll(cp.code);
                          globalName = "printInt";
                      } else if (type == IR.Type.BOOL) {
                    	  srcList.add(cp.src);
                		  instList.addAll(cp.code);
                          globalName = "printBool";
                      }
        		  }
        	  }
          }
		  IR.Global global = new IR.Global(globalName);
		  instList.add(new IR.Call(global, false, srcList));
	  }	  
	  return instList;
  }

  // Return ---  
  // Exp val;
  //
  // Codegen Guideline: 
  // 1. If val is non-null, generate IR code for it, and generate an IR.Return
  //    with its value
  // 2. Otherwise, generate an IR.Return with no value
  //
  static List<IR.Inst> gen(Ast.Return n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  
	  if(n.val != null) {
		  CodePack cp = gen(n.val, cinfo, env);
		  instList.addAll(cp.code);
		  IR.Src source = cp.src;
		  if(n.val instanceof Ast.Id && globalVars.get(((Ast.Id)n.val).nm) != null) {
			  IR.Temp temp = new IR.Temp();
			  ClassInfo ci = classEnv.get(objToClass.get(((Ast.Id)n.val).nm));
			  IR.Type type = gen(ci.fieldType(((Ast.Id)n.val).nm));
			  int offsetSize = ci.fieldOffset(((Ast.Id)n.val).nm);
			  
			  Ast.Field field = new Ast.Field(new Ast.This(), ((Ast.Id)n.val).nm);
			  AddrPack ap = genAddr(field, cinfo, env);
			  
			  instList.add(new IR.Load(type, temp, new IR.Addr(thisObj, offsetSize)));
			  source = temp;
		  }
		  
		  instList.add(new IR.Return(source));
		  
	  } else {
		  instList.add(new IR.Return());
	  }
	  
	  return instList;
  }

  // EXPRESSIONS

  // 1. Dispatch a generic gen() call to a specific gen() routine
  //
  static CodePack gen(Ast.Exp n, ClassInfo cinfo, Env env) throws Exception {
    if (n instanceof Ast.Call)     return gen((Ast.Call) n, cinfo, env);
    if (n instanceof Ast.NewObj)   return gen((Ast.NewObj) n, cinfo, env);
    if (n instanceof Ast.Field)    return gen((Ast.Field) n, cinfo, env);
    if (n instanceof Ast.Id)       return gen((Ast.Id) n, cinfo, env);
    if (n instanceof Ast.This)     return gen((Ast.This) n, cinfo);
    if (n instanceof Ast.IntLit)   return gen((Ast.IntLit) n);
    if (n instanceof Ast.BoolLit)  return gen((Ast.BoolLit) n);
    throw new GenException("Exp node not supported in this codegen: " + n);
  }

  // 2. Dispatch a generic genAddr call to a specific genAddr routine
  //    (Only one LHS Exp needs to be implemented for this assignment)
  //
  static AddrPack genAddr(Ast.Exp n, ClassInfo cinfo, Env env) throws Exception {
    if (n instanceof Ast.Field) return genAddr((Ast.Field) n, cinfo, env);
    throw new GenException(" LHS Exp node not supported in this codegen: " + n);
  }

  // Call ---
  // Exp obj; 
  // String nm;
  // Exp[] args;
  //
  static CodePack gen(Ast.Call n, ClassInfo cinfo, Env env) throws Exception {
    if (n.obj != null)
	return handleCall(n.obj, n.nm, n.args, cinfo, env, true);
    throw new GenException("In Call, obj is null: " + n);  
  } 
  
  // NewObj ---
  // String nm;
  //
  // Codegen Guideline: 
  //  1. Use class name to find the corresponding ClassInfo record from classEnv
  //  2. Find the class's type and object size from the ClassInfo record
  //  3. Cosntruct a malloc call to allocate space for the object
  //  4. Store a pointer to the class's descriptor into the first slot of
  //     the allocated space
  //
  static CodePack gen(Ast.NewObj n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Src> srcList = new ArrayList<IR.Src>();
	  List<IR.Inst> instList = new ArrayList<IR.Inst>();
	  ClassInfo ciBase = classEnv.get(n.nm);
	  IR.IntLit arg = new IR.IntLit(ciBase.objSize);
	  
	  IR.Temp temp = new IR.Temp();
	  srcList.add(arg);
	  instList.add(new IR.Call(new IR.Global("malloc"), false, srcList, temp));
	  
	  instList.add(new IR.Store(IR.Type.PTR, new IR.Addr(temp), new IR.Global("class_" + n.nm)));
	  
	  return new CodePack(IR.Type.PTR, temp, instList);
  }
  
  // Field ---
  // Exp obj; 
  // String nm;
  //
  
  // 1. gen()
  //
  // Codegen Guideline: 
  //   1.1 Call genAddr() to generate field variable's address
  //   1.2 Add an IR.Load to get its value
  //
  static CodePack gen(Ast.Field n, ClassInfo cinfo, Env env) throws Exception {
	  List<IR.Inst> instList = new ArrayList<IR.Inst>(); 
	  AddrPack addrPack = genAddr(n, cinfo, env);
	  instList.addAll(addrPack.code);
	  
	  IR.Id id = new IR.Id(n.nm);	  
	  IR.Load load = new IR.Load(addrPack.type, id, addrPack.addr);
	  instList.add(load);
	  
	  return new CodePack(addrPack.type, id, addrPack.code);
  }
  
  // 2. genAddr()
  //
  // Codegen Guideline: 
  //   2.1 Call gen() on the obj component
  //   2.2 Call getClassInfo() on the obj component to get base ClassInfo
  //   2.3 Access base ClassInfo rec to get field variable's offset
  //   2.4 Generate an IR.Addr based on the offset
  //
  static AddrPack genAddr(Ast.Field n, ClassInfo cinfo, Env env) throws Exception {
	  CodePack cpTemp = gen(n.obj, cinfo, env);
	  ClassInfo ciBase = getClassInfo(n.obj, cinfo, env);
	  IR.Addr addr = new IR.Addr(cpTemp.src, ciBase.fieldOffset(n.nm));
	   
	  return new AddrPack(cpTemp.type, addr, cpTemp.code);
  }
  
  // Id ---
  // String nm;
  //
  // Codegen Guideline: 
  //  1. Check to see if the Id is in the env.
  //  2. If so, it means it is a local variable or a parameter. Just return
  //     a CodePack containing the Id.
  //  3. Otherwise, the Id is an instance variable. Convert it into an
  //     Ast.Field node with Ast.This() as its obj, and invoke the gen() routine 
  //     on this new node
  //
  static CodePack gen(Ast.Id n, ClassInfo cinfo, Env env) throws Exception {
	  if(env.containsKey(n.nm)) {
		  IR.Type type = gen(env.get(n));
		  
		  return new CodePack(type, new IR.Id(n.nm));
	  } else {
		  Ast.Field tempField = new Ast.Field(new Ast.This(), n.nm);
		  return gen(tempField, cinfo, env);
	  }
  }

  // This ---
  //
  static CodePack gen(Ast.This n, ClassInfo cinfo) throws Exception {
    return new CodePack(IR.Type.PTR, thisObj);
  }

  // IntLit ---
  // int i;
  //
  static CodePack gen(Ast.IntLit n) throws Exception {
    return  new CodePack(IR.Type.INT, new IR.IntLit(n.i));
  }

  // BoolLit ---
  // boolean b;
  //
  static CodePack gen(Ast.BoolLit n) throws Exception {
    return  new CodePack(IR.Type.BOOL, n.b ? IR.TRUE : IR.FALSE);
  }

  // StrLit ---
  // String s;
  //
  static CodePack gen(Ast.StrLit n) throws Exception {
    return new CodePack(null, new IR.StrLit(n.s));
  }

  // Type mapping (AST -> IR)
  //
  static IR.Type gen(Ast.Type n) throws Exception {
    if (n == null)                  return null;
    if (n instanceof Ast.IntType)   return IR.Type.INT;
    if (n instanceof Ast.BoolType)  return IR.Type.BOOL;
    if (n instanceof Ast.ArrayType) return IR.Type.PTR;
    if (n instanceof Ast.ObjType)   return IR.Type.PTR;
    throw new GenException("Invali)d Ast type: " + n);
  }

}
