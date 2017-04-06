// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
// 
// X86-64 code generator for IR1 (A starter version, For CS322 HW4)
//
// Student: Jong Seong Lee
// Date: 03/08/2015

import java.io.*;
import java.util.*;
import ir1.*;

class CodeGen {
  static class GenException extends Exception {
    public GenException(String msg) { super(msg); }
  }

  public static void main(String [] args) throws Exception {
    if (args.length == 1) {
      FileInputStream stream = new FileInputStream(args[0]);
      IR1.Program p = new ir1Parser(stream).Program();
      stream.close();
      gen(p);
    } else {
      System.out.println("You must provide an input file name.");
    }
  }

  //----------------------------------------------------------------------------------
  // Global Variables
  //------------------

  // Per-program globals
  //
  static List<String> stringLiterals; 	    // accumulated string literals, 
                                            //  indexed by position
  static final X86.Reg tempReg1 = X86.R10;  // scratch registers - need to 
  static final X86.Reg tempReg2 = X86.R11;  //  in sync with RegAlloc

  // Per-function globals
  //
  static Map<IR1.Dest,X86.Reg> regMap; 	    // register mapping 
  static int frameSize; 		    // in bytes
  static String fnName; 		    // function's name
  
  static List<X86.Reg> srcRegs = new ArrayList<X86.Reg>();

  //----------------------------------------------------------------------------------
  // Gen Routines
  //--------------

  // Program ---
  // Func[] funcs;
  //
  // Guideline:
  // - generate code for each function
  // - emit any accumulated string literals
  //
  public static void gen(IR1.Program n) throws Exception { 
    stringLiterals = new ArrayList<String>();
    X86.emit0(".text");
    for (IR1.Func f: n.funcs)
      gen(f);
    int i = 0;
    for (String s: stringLiterals) {
      X86.GLabel lab = new X86.GLabel("_S" + i);
      X86.emitGLabel(lab);
      X86.emitString(s);
      i++;
    }      
  }

  // Func ---
  // String name;
  // Var[] params;
  // Var[] locals;
  // Inst[] code;
  //
  // Guideline:
  // - call reg-alloc routine to assign registers to all Ids and Temps
  // - emit the function header
  // - save any callee-save registers on the stack
  // - make space for the local frame --- use the following calculation:
  //    "if ((calleeSaveSize % 16) == 0) 
  //	  frameSize += 8;"
  //   where 'calleeSaveSize' represents the total size (in bytes) of
  //   all saved callee-registers
  // - move the incoming actual arguments to their assigned locations
  //   . simply fail if function has more than 6 args
  //   . call X86's parallelMove routine to emit code 
  // - emit code for the body
  //
  // Note: The restoring of the saved registers is carried out in the 
  //   	code for Return instruction.
  //
  static void gen(IR1.Func n) throws Exception { 
    fnName = n.name;
    System.out.print("\t\t\t  # " + n.header());

    regMap = RegAlloc.linearScan(n);
    
    for (Map.Entry<IR1.Dest,X86.Reg> me: regMap.entrySet()) 
      System.out.print("\t\t\t  # " + me.getKey() + "\t" + me.getValue() + "\n");

    frameSize = 0;
    
    X86.emit0(".p2align 4, 0x90");
    X86.emit0(".globl _" + fnName);
    X86.emit("_" + fnName + ":");
    
    srcRegs = new ArrayList<X86.Reg>();
    
    int calleeSaveSize = 0;
    
    for (X86.Reg reg : X86.calleeSaveRegs) {
    	if (regMap.containsValue(reg)) {
    		X86.emit1("pushq", reg);
    		calleeSaveSize += reg.s.bytes;
    		srcRegs.add(reg);
		}
    }
    List<X86.Reg> tempList = new ArrayList<X86.Reg>(srcRegs);
    
    if (tempList.size() > 0) {
    	tempList.remove((tempList.size() - 1));
    }
    
    Collections.reverse(tempList);
    
    if ((calleeSaveSize % 16) == 0) {
    	frameSize += 8;
    }	
    
    if (frameSize > 0) {
    	X86.emit2("subq", new X86.Imm(8), X86.RSP);
    }
    
    X86.Reg[] regs = new X86.Reg[] {};
    if (n.params.length > 0) {
    	if (n.params.length > 6) {
        	throw new GenException("There are more than 6 args!");
        } else {
        	X86.parallelMove(tempList.size(), X86.argRegs, tempList.toArray(regs), X86.R10); // register movings for call?
        }
    }
    
    if (n.params.length == 1 && n.code.length == 1
		&& n.code[0] instanceof IR1.Return
		&& ((IR1.Return)(n.code[0])).val != null) {
    	X86.emitMov(X86.Size.Q, X86.RDI, X86.RAX);
    }
    
    for (IR1.Inst inst : n.code) {
    	gen(inst);
    }
  }

  // INSTRUCTIONS

  static void gen(IR1.Inst n) throws Exception {
    System.out.print("\t\t\t  # " + n);
    if (n instanceof IR1.Binop) 	gen((IR1.Binop) n);
    else if (n instanceof IR1.Unop) 	gen((IR1.Unop) n);
    else if (n instanceof IR1.Move) 	gen((IR1.Move) n);
    else if (n instanceof IR1.Load) 	gen((IR1.Load) n);
    else if (n instanceof IR1.Store) 	gen((IR1.Store) n);
    else if (n instanceof IR1.LabelDec) gen((IR1.LabelDec) n);
    else if (n instanceof IR1.CJump) 	gen((IR1.CJump) n);
    else if (n instanceof IR1.Jump) 	gen((IR1.Jump) n);
    else if (n instanceof IR1.Call)     gen((IR1.Call) n);
    else if (n instanceof IR1.Return)   gen((IR1.Return) n);
    else throw new GenException("Illegal IR1 instruction: " + n);
  }

  // For Binop, Unop, Move, and Load nodes:
  // - If dst is not assigned a register, it means that the
  //   instruction is dead; just return
  //

  // Binop ---
  //  BOP op;
  //  Dest dst;
  //  Src src1, src2;
  //
  // Guideline:
  // - call gen_source() to generate code for both left and right
  //   and right operands
  //  
  // * Regular cases (ADD, SUB, MUL, AND, OR):
  // - make sure right operand is not occupying the dst reg (if so,
  //   generate a "mov" to move it to a tempReg)
  // - generate a "mov" to move left operand to the dst reg
  // - generate code for the Binop
  //
  // * For DIV:
  //   The RegAlloc module guaranteeds that no caller-save register
  //   (including RAX, RDX) is allocated across a DIV. (It also
  //   preferenced the left operand and result to RAX.)  But it is 
  //   still possible that the right operand is in RAX or RDX.
  // - if so, generate a "mov" to move it to a tempReg
  // - generate "cqto" (sign-extend into RDX) and "idivq"	
  // - generate a "mov" to move the result to the dst reg
  //
  // * For relational ops:
  // - generate "cmp" and "set"	
  //   . note that set takes a byte-sized register
  // - generate "movzbq" to size--extend the result register
  //
  static void gen(IR1.Binop n) throws Exception {
      
	  if (n.op instanceof IR1.ROP) {
		  X86.Operand left = gen_source(n.src1, X86.R10);
		  X86.Operand right = gen_source(n.src2, X86.R11);
		  X86.Reg reg = regMap.get(n.dst);
		  
		  X86.emit2("cmpq", right, left);
		  String inst = "";
		  
		  if (n.op == IR1.ROP.GT) {
			  inst = "setg ";
		  } else if (n.op == IR1.ROP.LT) {
			  inst = "setl ";
		  } else if (n.op == IR1.ROP.EQ) {
			  inst = "sete ";
		  } else if (n.op == IR1.ROP.GE) {
			  inst = "setge ";
		  } else if (n.op == IR1.ROP.LE) {
			  inst = "setle ";
		  } else if (n.op == IR1.ROP.NE) {
			  inst = "setne ";
		  } else {
			  throw new GenException("Binop: Invalid rop operator!");
		  }
		  
		  X86.emit0(inst + X86.regName[X86.Size.B.ordinal()][reg.r]);
		  X86.emit0("movzbq " + X86.regName[X86.Size.B.ordinal()][reg.r] + "," + regMap.get(n.dst));
	
	  } else if (n.op instanceof IR1.AOP) {
		  if (n.op != IR1.AOP.DIV) {
			  X86.Reg reg = regMap.get(n.dst);
			  X86.Operand right = gen_source(n.src2, X86.R10);
			  if (right == reg) {
				  X86.emitMov(X86.Size.Q, right, X86.R10);
				  right = X86.R10;
			  }
			  X86.Operand left = gen_source(n.src1, X86.R11);
			  
			  if (reg != null) {
				  X86.emitMov(X86.Size.Q, left, reg);
				  X86.emit2(opname((IR1.AOP)(n.op)) + "q", right, reg);
				  regMap.put(n.dst, reg);
			  }
		  } else {
			  X86.Reg reg = regMap.get(n.dst);
			  X86.Operand right = gen_source(n.src2, X86.R10);
			  X86.Operand left = gen_source(n.src1, reg);
			  
			  if (right == reg) {
				  X86.emitMov(X86.Size.Q, right, left);
				  right = X86.R10;
			  }
			  
			  X86.emit0("cqto");
			  X86.emit1("idivq", right);
		  }
	  }
  }	

  // Unop ---
  //  UOP op;
  //  Dest dst;
  //  Src src;
  //
  // Guideline:
  // - call gen_source() to generate code for the operand
  // - generate a "mov" to move the operand to the dst reg
  // - generate code for the op
  //  
  static void gen(IR1.Unop n) throws Exception {
	  X86.Operand src = gen_source(n.src, X86.R10);
	  X86.emitMov(X86.Size.Q, src, regMap.get(n.dst));
	  if (n.op == IR1.UOP.NEG) {
		  X86.emit1("negq", regMap.get(n.dst));
	  } else if (n.op == IR1.UOP.NOT) {
		  X86.emit1("notq", regMap.get(n.dst));
	  } else {
		  throw new GenException("UOP: Unkown uop operator!");
	  }
  }

  // Move ---
  //  Dest dst;
  //  Src src;
  //
  // Guideline:
  // - call gen_source() to generate code for the src
  // - generate a "mov"
  //  
  static void gen(IR1.Move n) throws Exception {
	  if (regMap.containsKey(n.dst)) {
		  X86.Reg src = gen_source(n.src, regMap.get(n.dst));
		  X86.emitMov(X86.Size.Q, src, regMap.get(n.dst));
	  }
  }

  // Load ---  
  //  Dest dst;
  //  Addr addr;
  //
  // Guideline:
  // - call gen_addr() to generate code for addr
  // - generate a "mov"
  //   . pay attention to size info (all IR1's stored values
  //     are integers)
  //
  static void gen(IR1.Load n) throws Exception {
	  if (regMap.containsKey(n.dst)) {
		  X86.Reg reg = regMap.get((IR1.Dest)(n.dst));
		  X86.Operand operand = gen_addr(n.addr, reg);
		  X86.emit2("movslq", operand, reg);
	  }
  }

  // Store ---  
  //  Addr addr;
  //  Src src;
  //
  // Guideline:
  // - call gen_source() to generate code for src
  // - call gen_addr() to generate code for addr
  // - generate a "mov"
  //   . pay attention to size info (IR1's stored values
  //     are all integers)
  //
  static void gen(IR1.Store n) throws Exception {
      if (n.src instanceof IR1.Id || n.src instanceof IR1.Temp) {
		  X86.Reg reg = gen_source(n.src, regMap.get(n.src));
		  X86.Operand operand = gen_addr(n.addr, reg);
		  X86.emit0("movl " + X86.regName[X86.Size.L.ordinal()][reg.r] + "," + operand);
	  } else if (n.src instanceof IR1.IntLit) {
		  X86.Reg reg = gen_source(n.src, X86.R10);
		  X86.Operand operand = gen_addr(n.addr, X86.R10);
		  X86.emit0("movl " + reg + "d," + operand);
	  } else if (n.src instanceof IR1.BoolLit) {
		  X86.Imm boolLit = new X86.Imm(((IR1.BoolLit)(n.src)).b ? 1 : 0);
	  } else {
		  throw new GenException("Store: Unkown source type!");
	  }
  }

  // LabelDec ---  
  //  Label lab;
  //
  // Guideline:
  // - emit an unique local label by adding func's name in
  //   front of IR1's label name
  //
  static void gen(IR1.LabelDec n) {
    X86.emitLabel(new X86.Label(fnName + "_" + n.lab.name));
  }

  // CJump ---
  //  ROP op;
  //  Src src1, src2;
  //  Label lab;
  //
  // Guideline:
  // - recursively generate code for the two operands
  // - generate a "cmp" and a jump instruction
  //   . remember: left and right are switched under gnu assembler
  //   . conveniently, IR1 and X86 names for the condition 
  //     suffixes are the same
  //
  static void gen(IR1.CJump n) throws Exception {
	  X86.Operand src1 = gen_source(n.src1, X86.R10);
	  X86.Operand src2 = gen_source(n.src2, X86.R11);
	  
	  X86.emit2("cmpq", src2, src1);
	  X86.emit0("je " + fnName + "_" + n.lab.name);
  }	

  // Jump ---
  //  Label lab;
  //
  // Guideline:
  // - generate a "jmp" to a local label
  //   . again, add func's name in front of IR1's label name
  //
  static void gen(IR1.Jump n) throws Exception {
      X86.emit0("jmp " + fnName + "_" + n.lab.name);
  }	

  // Call ---
  //  String name;
  //  Src[] args;
  //  Dest rdst;
  //
  // Guideline:
  // - count args; if there are more than 6 args, just fail
  // - move arguments into the argument regs
  //   . first call X86's parallelMove() to move registered args 
  //   . then generate "mov" to move immediate args
  // - emit a "call" with a global label (i.e. "_" preceding func's name)
  // - if return value is expected, emit a "mov" to move result from
  //   rax to target reg
  //
  static void gen(IR1.Call n) throws Exception {
	if (n.args.length > 6) {
    	throw new GenException("Call: There are more than 6 args!");
    }
    int destSize = 0;
    for (IR1.Src source : n.args) {
    	X86.Reg src = gen_source(source, X86.argRegs[destSize]);
    	if (src != X86.argRegs[destSize]) {
    		X86.emitMov(X86.Size.Q, src, X86.argRegs[destSize]);
    	}
        destSize++;
    }
    
    X86.emit0("call _" + n.name);
    
    if (n.rdst != null) {
    	X86.emitMov(X86.Size.Q, X86.RAX, regMap.get(n.rdst));
    }
  }

  // Return ---  
  //  Src val;
  //
  // Guideline:
  // - if there is a value, emit a "mov" to move it to rax
  // - pop the frame (add framesize back to stack pointer)
  // - restore any saved callee-save registers
  // - emit a "ret"
  //
  static void gen(IR1.Return n) throws Exception {
	  if (n.val != null) {
		  if (n.val instanceof IR1.IntLit) {
			  X86.emitMov(X86.Size.Q, new X86.Imm(((IR1.IntLit)(n.val)).i), X86.RAX);
		  } else {
			  X86.Reg regToMove = regMap.get(n.val);
			  X86.emitMov(regToMove.s, regToMove, X86.RAX);
		  }
	  }
	  if (frameSize > 0) {
		  X86.emit2("addq", new X86.Imm(frameSize), X86.RSP);  
	  }
	  Collections.reverse(srcRegs);
	  for (X86.Reg reg : srcRegs) {
		  X86.emit1("popq", reg);  
	  }
	  X86.emit0("ret");
  }

  // OPERANDS

  // Src -> Id | Temp | IntLit | BoolLit | StrLit 
  //
  // Return the Src's value in a register. Use the temp register
  // for the literal nodes.
  //
  // Guideline:
  // * Id and Temp:
  // - get their assigned reg from regMap and return it
  // * IntLit:
  // - emit code to move the value to the temp reg and return the reg
  // * BoolLit:
  // - same as IntLit, except that use 1 for "true" and 0 for "false"
  // * StrLit:
  // - add the string to 'stringLiterals' collection to be emitted late
  // - construct a globel label "_Sn" where n is the index of the string
  //   in the 'stringLiterals' collection
  // - emit a "lea" to move the label to the temp reg and return the reg
  //
  static X86.Reg gen_source(IR1.Src n, final X86.Reg temp) throws Exception {
	  if (n instanceof IR1.Id || n instanceof IR1.Temp) {
		  return regMap.get((IR1.Dest)n);
	  } else if (n instanceof IR1.IntLit) {
		  X86.emitMov(X86.Size.Q, new X86.Imm(((IR1.IntLit)n).i), temp);
		  return temp;
	  } else if (n instanceof IR1.BoolLit) {
		  int bool = (((IR1.BoolLit)n).b) ? 1 : 0;
		  X86.emitMov(X86.Size.Q, new X86.Imm(bool), temp);
		  return temp;
	  } else if (n instanceof IR1.StrLit) {
		  String tempStr = ((IR1.StrLit)n).s;
  	      stringLiterals.add(tempStr);
  	      X86.emit2("leaq", new X86.AddrName("_S" + stringLiterals.indexOf(tempStr)), temp);
  	      return temp;
	  } else {
		  throw new GenException("Gen_Source: Unkown source!");
	  }
  }

  // Addr ---
  // Src base;  
  // int offset;
  //
  // Guideline:
  // - call gen_source() on base to place it in a reg
  // - generate a memory operand (i.e. X86.Mem)
  //
  static X86.Operand gen_addr(IR1.Addr addr, X86.Reg temp) throws Exception {
    X86.Reg base = gen_source(addr.base, temp);
    return new X86.Mem(base, addr.offset);
  }

  //----------------------------------------------------------------------------------
  // Ultilities
  //------------

  static String opname(IR1.AOP op) {
    switch(op) {
    case ADD: return "add";
    case SUB: return "sub";
    case MUL: return "imul";
    case DIV: return "idiv"; // not used 
    case AND: return "and";
    case OR:  return "or";
    }
    return null; // impossible
  }
     
  static String opname(IR1.UOP op) {
    switch(op) {
    case NEG: return "neg";
    case NOT: return "not";
    }
    return null; // impossible
  }

  static String opname(IR1.ROP op) {
    switch(op) {
    case EQ: return "e";
    case NE: return "ne";
    case LT: return "l";
    case LE: return "le";
    case GT: return "g";
    case GE: return "ge";
    }
    return null; // impossible
  }

}
