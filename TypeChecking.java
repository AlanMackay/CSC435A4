// TypeChecking.java
//

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.lang.Class;

public class TypeChecking {

	// Checks whether a value of type srcTyp can be assigned to or compared with
	// a value/variable of type destType; argument ctx is used only for line number info
	// Assignability is defined in the Go specification:
	//   https://golang.org/ref/spec#Assignability
	// This code is incomplete because it does not handle assignment of nil to pointer variables,
	// and it should handle multiple assignment.
	// Note that this method should make use of the identicalTypes method defined below.
	public static boolean checkAssignability(Type destTyp, Type srcTyp, ParserRuleContext ctx) {
		// handle the obvious case!
		if (destTyp == srcTyp) return true;
		if (identicalTypes(destTyp, srcTyp) || (destTyp.getName().equals(srcTyp.getName()))) return true;

		// avoid error messages when type is unknown, allow arbitrary dest types
		// for some of the methiods in imported packages
		if (destTyp == Type.unknownType || destTyp == Type.anyType)
		    return true;
		if (srcTyp == Type.unknownType) return true;

		// Assignment of nil to pointer variables
		if (srcTyp instanceof Type.Pointer && destTyp instanceof Type.Pointer){
			if( ((Type.Pointer)srcTyp).getBaseType() == Type.anyType){
				return true;
			}
		}

		assert srcTyp != null;
		assert destTyp != null;

		// handle case when src is an untyped numeric constant
		if (srcTyp instanceof Type.UntypedNumber) {
			if (destTyp instanceof Type.Flt) return true;

			// Check whether the number will fit into the particular size of int provided for destTyp
			// Since the untyped integer number is stored in a 64-bit long datatype,
			// very large numbers becomes a problem. When the destination type is an 
			// int64 or uint64 we compare string representations instead of numeric values.
			String strNum = srcTyp + "";
			String cleanNum = strNum.replaceAll("[^0-9]","");
			boolean error = false;
			long number = 0;
			long minValue = 0;
			long maxValue = 0;
			if (destTyp instanceof Type.Int){
				if(((Type.Int)destTyp).getSize() == 64){ // Check string representation
					if(cleanNum.length() > 19)
						error = true;
					// Strings must be equal length when comparing since "9" > "10" 
					else if ( (cleanNum.compareTo("9223372036854775808")) > 0 && cleanNum.length() == 19) 
						error = true;
					else if( ((cleanNum.compareTo("9223372036854775807")) > 0 &&  cleanNum.length() == 19) && 
						!(strNum.contains("-")))
						error = true;
				}
				else{ // Check numeric value
					number = ((Type.UntypedNumber)srcTyp).getIntValue();
					minValue = -((long)1 << ( ((Type.Int)destTyp).getSize() - 1) ); // -(2^(destTyp size - 1))
					maxValue = ((long)1 << ( ((Type.Int)destTyp).getSize() - 1) ) - 1; // 2^(destTyp size - 1) - 1
				}
			} else if (destTyp instanceof Type.Uint){ // Check string representation
				if(((Type.Uint)destTyp).getSize() == 64){
					if(strNum.contains("-") || cleanNum.length() > 20)
						error = true;
					// Strings must be equal length when comparing since "9" > "10" 
					else if((cleanNum.compareTo("18446744073709551615") > 0 &&  cleanNum.length() == 20)) 				
						error = true;
				}
				else{ // Check numeric value
					number = ((Type.UntypedNumber)srcTyp).getIntValue();
					minValue = 0;
					maxValue = ((long)1 << (((Type.Uint)destTyp).getSize()) ) - 1; // 2^(destTyp size) - 1
				}
			} else
				return false;

			// Print error if overflow occurs
			if(error || number < minValue || number > maxValue){
				ReportError.error(ctx, "Untyped number " + srcTyp + " overflows " + destTyp);
				return false;
			}

			return ((Type.UntypedNumber)srcTyp).isInteger();
		}
	
		// handle initialization of an array or slice
		// Note: this code should be expanded to also handle the destination
		// being a TypeList too ... that's needed for multiple assignment as in
		//      str, x = "abc", 26
		if (srcTyp instanceof Type.TypeList) {
			if (destTyp instanceof Type.Array || destTyp instanceof Type.Slice) {
				// check element types
				Type et = destTyp instanceof Type.Array?
						((Type.Array)destTyp).getElementType() :
						((Type.Slice)destTyp).getElementType() ;
				for( Type t : ((Type.TypeList)srcTyp).getTypes() ) {
					if (!checkAssignability(et,t,ctx)) return false;
				}
				return true;
			} else if (destTyp instanceof Type.TypeList){

				Type[] destTypes = ((Type.TypeList)srcTyp).getTypes();
				int i = 0;
				for( Type t : ((Type.TypeList)srcTyp).getTypes() ) {
					if (!checkAssignability(destTypes[i],t,ctx)) return false;
					i++;
				}
				return true;
			}
		}

		ReportError.error(ctx, "type "+srcTyp.toString()+" is incompatible with "+destTyp.toString());
		return false;
	}

	// Checks if the function with signature fntyp can be called with the argument
	// types actualTypes. The result is the function result type.
	// This code is believed to be complete!
    public static Type checkFunctionCall( Type.Function fntyp, Type[] actualTypes, ParserRuleContext ctx ) {
        Type[] formalTypes = fntyp.getParameters();
        int i = 0;
        for( int k = 0; k<actualTypes.length; k++ ) {
            if (i >= formalTypes.length) {
                ReportError.error(ctx, "too many arguments in function call");
                break;
            }
            if (formalTypes[i] == Type.variadicAnyType)
                break;  // no need to check further
            checkAssignability(formalTypes[i], actualTypes[k], ctx);
            i++;
        }
        if (actualTypes.length < formalTypes.length && formalTypes[i] != Type.variadicAnyType)
            ReportError.error(ctx, "too few arguments in function call");
		Type[] restyp = fntyp.getResults();
		if (restyp.length == 0) return Type.voidType;
		assert restyp[0] != null;
		return restyp[0];
	}
 
 	// This function tests if two types have the same underlying types
 	// as explained in the Go specification:
 	//    https://golang.org/ref/spec#Types
 	public static boolean sameUnderlyingTypes( Type a, Type b ) {
 		if (a.getClass() != b.getClass()) return false;
 		if (a == b) return true;
 		if (a instanceof Type.Array) {
 			Type.Array aa = (Type.Array)a;
 			Type.Array bb = (Type.Array)b;
 			return aa.getElementType() == bb.getElementType();
 		}
 		if (a instanceof Type.Slice) {
 			Type.Slice aa = (Type.Slice)a;
 			Type.Slice bb = (Type.Slice)b;
 			return aa.getElementType() == bb.getElementType();
 		}
 		if (a instanceof Type.Pointer) {
 			Type.Pointer aa = (Type.Pointer)a;
 			Type.Pointer bb = (Type.Pointer)b;
 			return aa.getBaseType() == bb.getBaseType();
 		}
 		if (a instanceof Type.Pointer) {
 			Type.Pointer aa = (Type.Pointer)a;
 			Type.Pointer bb = (Type.Pointer)b;
 			return aa.getBaseType() == bb.getBaseType();
 		}
 		// does that cover all the cases?
 		return false;
 	}
 	
 	// This tests for Type Identity as described in the Go specification:
 	//    https://golang.org/ref/spec#Type_identity
 	public static boolean identicalTypes( Type a, Type b ) {
 		if (a.isNamedType()) {
 			// if two types are named differently, they are not identical!
 			if (b.isNamedType())
 				return a.getName().equals(b.getName());
 			return false;
 		}
 		if (b.isNamedType())
 			return false;
 		if (a.getClass() != b.getClass()) return false;
 		if (a instanceof Type.Array) {
 			Type.Array aa = (Type.Array)a;
 			Type.Array bb = (Type.Array)b;
 			return (aa.getSize() == bb.getSize()) &&
 				identicalTypes(aa.getElementType(), bb.getElementType());
 		}
 		if (a instanceof Type.Slice) {
 			Type.Slice aa = (Type.Slice)a;
 			Type.Slice bb = (Type.Slice)b;
 			return identicalTypes(aa.getElementType(), bb.getElementType());
 		}
 		if (a instanceof Type.Pointer) {
 			Type.Pointer aa = (Type.Pointer)a;
 			Type.Pointer bb = (Type.Pointer)b;
 			return identicalTypes(aa.getBaseType(), bb.getBaseType());
 		}
 		if (a instanceof Type.Struct) {
 			Type.Struct aa = (Type.Struct)a;
 			Type.Struct bb = (Type.Struct)b;	
 			LinkedHashMap<String, Symbol> af = aa.getFields();
 			LinkedHashMap<String, Symbol> bf = bb.getFields();
 			if (af.size() != bf.size())
 				return false;
 			Iterator<Symbol> av = af.values().iterator();
 			Iterator<Symbol> bv = bf.values().iterator();
 			while(av.hasNext()) {
 				Symbol as = (Symbol)av.next();
 				Symbol bs = (Symbol)bv.next();
 				if (!as.getName().equals(bs.getName()))
 					return false;
 				if (!identicalTypes(as.getType(), bs.getType()))
 					return false;
 			}
 			return true;
 		}
 		if (a instanceof Type.Function) {
 			Type.Function aa = (Type.Function)a;
 			Type.Function bb = (Type.Function)b;
 			Type[] ap = aa.getParameters();
 			Type[] bp = bb.getParameters();
 			if (ap.length != bp.length) return false;
 			for(int i=0; i<ap.length; i++) {
 				if (!identicalTypes(ap[i], bp[i])) return false;
 			}
 			ap = aa.getResults();
 			bp = bb.getResults();
 			if (ap.length != bp.length) return false;
 			for(int i=0; i<ap.length; i++) {
 				if (!identicalTypes(ap[i], bp[i])) return false;
 			}
 			return true;
 		}
 		// did we cover everything?
 		return false;
 	}


 	// Report an error if the operator is not applicable to the operand types;
 	// return the type of the result
	public static Type checkBinOp(Type lhs, Type rhs, String op, ParserRuleContext ctx) {
    	// very much code is missing here!
    	if(!(checkAssignability(lhs, rhs, ctx) || (lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber))){
    		ReportError.error(ctx, "Left hand side (" + lhs + ") cannot be assigned right hand side (" + rhs + ")");
    		return Type.unknownType;
    	}
    	switch (op) {
    		case "+":
    			if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
    				Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()) num = (ulhs.getIntValue() + urhs.getIntValue() + ""); 
    				else num = (ulhs.getDoubleValue() + urhs.getDoubleValue() + "");
    				return Type.newUntypedNumber(num);
    			}
    			if(lhs instanceof Type.Int || lhs instanceof Type.Uint || lhs instanceof Type.Flt || lhs == Type.stringType) break;
    			else ReportError.error(ctx, "Operator \""+ op + "\" cannot be used on type " + lhs.toString());
 				return Type.unknownType;   		
    		case "-":
    			if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
    				Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()) num = (ulhs.getIntValue() - urhs.getIntValue() + "");
    				else num = (ulhs.getDoubleValue() - urhs.getDoubleValue() + "");
    				return Type.newUntypedNumber(num);
    			}
    			if(lhs instanceof Type.Int || lhs instanceof Type.Uint || lhs instanceof Type.Flt) break;
    			else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;   	
			case "*":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()) num = (ulhs.getIntValue() * urhs.getIntValue() + "");
    				else num = (ulhs.getDoubleValue() * urhs.getDoubleValue() + "");
    				return Type.newUntypedNumber(num);
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint || lhs instanceof Type.Flt) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "/":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()) num = (ulhs.getIntValue() / urhs.getIntValue() + "");
    				else num = (ulhs.getDoubleValue() / urhs.getDoubleValue() + "");
    				return Type.newUntypedNumber(num);
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint || lhs instanceof Type.Flt) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "%":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()) {
    					num = (ulhs.getIntValue() % urhs.getIntValue() + "");
    					return Type.newUntypedNumber(num);
					}			
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "&":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() & urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "|":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() | urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "^":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() ^ urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "&^":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() & ~urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int || lhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on type " + lhs.toString());
				return Type.unknownType;
			case "<<":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() << urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int && rhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on types " + lhs.toString() + " and " + rhs.toString());
				return Type.unknownType;
			case ">>":
				if(lhs instanceof Type.UntypedNumber && rhs instanceof Type.UntypedNumber){
					Type.UntypedNumber ulhs = (Type.UntypedNumber)lhs;
    				Type.UntypedNumber urhs = (Type.UntypedNumber)rhs;
    				String num;
    				if(ulhs.isInteger()){ 
    					num = ((ulhs.getIntValue() >> urhs.getIntValue()) + "");
    					return Type.newUntypedNumber(num);
    				}
				}
				if(lhs instanceof Type.Int && rhs instanceof Type.Uint) break;
				else ReportError.error(ctx, "Operator \"" + op + "\" cannot be used on types " + lhs.toString() + " and " + rhs.toString());
				return Type.unknownType;
			case "==":
				return Type.boolType;
			case "!=":
				return Type.boolType;
			case "<":
				return Type.boolType;
			case "<=":
				return Type.boolType;	
			case ">":
				return Type.boolType;
			case ">=":
				return Type.boolType;		
			case "&&":
				return Type.boolType;
			case "||":
				return Type.boolType;														
    	}

    	return lhs;
    }

 	// Report an error if the operator is not applicable to the operand type;
 	// return the type of the result
	public static Type checkUnaryOp(Type opnd, String op, ParserRuleContext ctx, boolean isVariable) {

		switch (op) {
	        case "+":  
				if (!(opnd instanceof Type.Int || opnd instanceof Type.Uint || opnd instanceof Type.UntypedNumber || opnd instanceof Type.Flt))
					ReportError.error(ctx, "The operator \"" + op +"\" can not be used on type " + opnd);
				else
					return opnd; // Operand type does not change
	            break;
	        case "-":  
	        	if (opnd instanceof Type.UntypedNumber){
	        		// Constant folding: -(2) => -2
	        		String strNum = opnd + "";
					String result = strNum.replaceAll("[^0-9.]","");
	        		result = "-" + result;
	            	return Type.newUntypedNumber(result);
	            }
				if (!(opnd instanceof Type.Int || opnd instanceof Type.Uint || opnd instanceof Type.Flt))
					ReportError.error(ctx, "The operator \"" + op +"\" can not be used on type " + opnd);
				else
					return opnd; // Operand type does not change
	        	break;
	        case "!":  
				if (opnd != Type.boolType) 
					ReportError.error(ctx, "The operator \"" + op +"\" can not be used on type " + opnd);
				else
					return opnd; // Operand type does not change
	            break;  
	        case "^": 
	        	if(opnd instanceof Type.UntypedNumber && ((Type.UntypedNumber)opnd).isInteger() 
	        		&& !((Type.UntypedNumber)opnd).isPossibleDouble()){
	        		// Constant folding
	        		String result = String.valueOf( -1 ^ (((Type.UntypedNumber)opnd).getIntValue()) );
	        		return Type.newUntypedNumber(result);
	        	}
	        	if (!(opnd instanceof Type.Int || opnd instanceof Type.Uint)) 
					ReportError.error(ctx, "The operator \"" + op +"\" can not be used on type " + opnd);
				else
					return opnd; // Operand type does not change
	            break;  
	        case "*": 
	        	if(!(opnd instanceof Type.Pointer))
	        		ReportError.error(ctx, "The operator \"" + op +"\" can not be used on type " + opnd);
	        	else
					return ((Type.Pointer)opnd).getBaseType(); // Return base type of pointer
	            break;                                       
	        case "&":
	        	if(isVariable)
	        		return Type.newPointerType(opnd); // Return a pointer with baseType "opnd"                       
	        	else
	        		ReportError.error(ctx, "The operator \"" + op +"\" must be used on a variable");
		}  

    	return Type.unknownType; // Operator is not applicable to the operand type
    }

}
