/* LLVMPredefined.java
 * 
 * Predefined functions and strings which need to be included in the generated
 * LLVM output file.
 * 
 * Author: Nigel Horspool
 * Date: March 2016
 */
 
import java.util.*;



public class LLVMPredefined {

    // predefined code to emit
    static final String[] predefined = {
        // in the following strings, <W> is replaced with pointer/int size (32 or 64)
        // and <A> is replaced with the alignment needed for pointers (4 or 8).
//    	"declare i<W> @strlen(i8*) #1",
//    	"declare i8* @malloc(i<W>) #1",
        "declare noalias i8* @calloc(i<W>, i<W>)",
//    	"declare i8* @strcpy(i8*, i8*) #1",
//    	"declare i8* @strcat(i8*, i8*) #1",
//      "declare i8* @strncpy(i8*, i8*, i<W>) #1",
    	"declare i<W> @printf(i8*, ...) #1",
//    	"declare i8* @gets(i8*) #1",
//      "declare i<W> @atoi(i8*) #1",
    	"declare void @llvm.memset.p0i8.i<W>(i8*, i8, i<W>, i32, i1)",
    	""
    };

    // Preamble for target triple: "i686-pc-mingw32"
    static public final String preamble32 = "\ntarget datalayout = " +
            "\"e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:" +
            "32:32-f64:64:64-f80:128:128-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32-S32\"\n";

    // Preamble for target triple: "x86_64-unknown-linux-gnu"
    // This is what is generated by clang on the linux teaching server: linux.csc.uvic.ca
    static public final String preamble64 = "\ntarget datalayout = " +
            "\"e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:" +
            "32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128\"\n";

    // Preamble for target triple: "x86_64-apple-macosx10.9.3"
    static public final String preambleMac64 = "target datalayout = " +
            "\"e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:" +
            "32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128\"\n";

    static public final String epilog32 = "\nattributes #0 = { nounwind \"less-precise-fpmad\"=\"false\" " +
        "\"no-frame-pointer-elim\"=\"true\" \"no-frame-pointer-elim-non-leaf\" " +
        "\"no-infs-fp-math\"=\"false\" \"no-nans-fp-math\"=\"false\" " +
        "\"stack-protector-buffer-size\"=\"8\" \"unsafe-fp-math\"=\"false\" "+
        "\"use-soft-float\"=\"false\" }\n" +
        "attributes #1 = { \"less-precise-fpmad\"=\"false\" \"no-frame-pointer-elim\"=\"true\" " +
        "\"no-frame-pointer-elim-non-leaf\" \"no-infs-fp-math\"=\"false\" " +
        "\"no-nans-fp-math\"=\"false\" \"stack-protector-buffer-size\"=\"8\" " +
        "\"unsafe-fp-math\"=\"false\" \"use-soft-float\"=\"false\" }\n";

    static public final String epilog64 = "\nattributes #0 = { nounwind uwtable \"less-precise-fpmad\"=\"false\" " +
        "\"no-frame-pointer-elim\"=\"true\" \"no-frame-pointer-elim-non-leaf\" " +
        "\"no-infs-fp-math\"=\"false\" \"no-nans-fp-math\"=\"false\" " +
        "\"stack-protector-buffer-size\"=\"8\" \"unsafe-fp-math\"=\"false\" "+
        "\"use-soft-float\"=\"false\" }\n" +
        "attributes #1 = { \"less-precise-fpmad\"=\"false\" \"no-frame-pointer-elim\"=\"true\" " +
        "\"no-frame-pointer-elim-non-leaf\" \"no-infs-fp-math\"=\"false\" " +
        "\"no-nans-fp-math\"=\"false\" \"stack-protector-buffer-size\"=\"8\" " +
        "\"unsafe-fp-math\"=\"false\" \"use-soft-float\"=\"false\" }\n";

    public static void writePredefinedCode( LLVM llvm ) {
        for(String s : predefined) {
            String ss = s;
            // a few lines have to be selectively included -- they are
            // tailored for use on the 8-byte and 4-byte platforms
            if (ss.startsWith("#if8")) {
                if (llvm.ptrAlign == 4) continue;
                ss = ss.substring(4);
            } else {
                if (ss.startsWith("#if4")) {
                    if (llvm.ptrAlign == 8) continue;
                    ss = ss.substring(4);
                }
            }
            if (llvm.macOS) {
                ss = ss.replaceAll(" #0", " ");  // causes errors with MacOS!
                ss = ss.replaceAll(" #1", " ");
            }
			ss = ss.replaceAll("\\<W\\>", ""+llvm.ptrSize);
			ss = ss.replaceAll("\\<A\\>", ""+llvm.ptrAlign);
            llvm.println(ss);
        }
    }
}