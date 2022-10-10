structure jack =
struct
open jackAS;
    
     structure jackLrVals = jackLrValsFun(structure Token = LrParser.Token) 
               
     structure jackLex = jackLexFun(structure Tokens = jackLrVals.Tokens)

     structure jackParser = Join(structure Lex= jackLex
                                structure LrParser = LrParser
                                structure ParserData = jackLrVals.ParserData)
                                  
     val input_line =
       fn f =>
          let val sOption = TextIO.inputLine f
          in
            if isSome(sOption) then
               Option.valOf(sOption)
            else
               ""
          end

     val jackparse = 
         fn filename =>
           let val instrm = TextIO.openIn filename
               val lexer = jackParser.makeLexer(fn i => input_line instrm)
               val _ = jackLex.UserDeclarations.pos := 1
               val error = fn (e,i:int,_) => 
                               TextIO.output(TextIO.stdOut," line " ^ (Int.toString i) ^ ", Error: " ^ e ^ "\n")
           in 
                jackParser.parse(30,lexer,error,()) before TextIO.closeIn instrm
           end

     (* These functions are needed for if-then-else expressions and functions *)
     val label = ref 0;

     fun nextLabel() = 
         let val lab = !label
         in 
           label := !label + 1;
           "L"^Int.toString(lab)
         end

	fun printC nil = ""
	| printC (h::t) = 
		let val
	temp = printC (t)
			in
			"push constant "^Int.toString(Char.ord(h))^"\ncall String.appendChar 2\n"^temp
			end
	(*fun allPrintC st outFile = 
	let val cList = String.explode(st)
		in	
		map printC cList outFile
		end*)




     (* a binding is a 4-tuple of (name, typ, segment, offset) *)
     exception unboundId;  
     
     (* find the type, segment and offset for an identifier *)
     fun boundTo(name:string,[]) = 
         (TextIO.output(TextIO.stdOut, "Unbound identifier "^name^" referenced!\n");
          raise unboundId)
       | boundTo(name,(n,typ,segment,offset)::t) = if name=n then (typ,segment,offset) else boundTo(name,t);

     (* create a list of bindings from a list of names in a particular segment *)
	 fun createBindings([],typ,segment,offset) = []
	   | createBindings(name::names,typ,segment,offset) = (TextIO.output(TextIO.stdOut,"generating binding for "^name^":"^typ^":"^segment^":"^Int.toString(offset)^"\n");
							       (name,typ,segment,offset)::createBindings(names,typ,segment,offset+1))

     (* create a list of bindings from class variables; sort them into static and field segments *)
     fun createClassBindings(cvList) = 
	 let fun ccbHelper([],soffset,foffset) = []
	       | ccbHelper((seg,typ,names)::t,soffset,foffset) =
		 if seg = "static" then
		     createBindings(names,typ,"static",soffset)@ccbHelper(t,soffset+length(names),foffset)
		 else
		     createBindings(names,typ,"this",foffset)@ccbHelper(t,soffset,foffset+length(names))
	 in
	     ccbHelper(cvList,0,0)
	 end

     (* create a list of bindings from parameters; each param is a (type,name) tuple *)
     fun createParamBindings([],offset) = []
       | createParamBindings((typ,name)::t,offset) = 
	 createBindings([name],typ,"argument",offset)@createParamBindings(t,offset+1)

     (* create a list of bindings from local variable declarations *)
     fun createLocalBindings(vardecs) =
	 let fun createLocalBindingsHelper([],offset) = []
	       | createLocalBindingsHelper((typ,names)::t,offset) = 
		 createBindings(names,typ,"local",offset)@createLocalBindingsHelper(t,offset+length(names))
	 in
	     createLocalBindingsHelper(vardecs,0)
	 end

     (* find the number of bindings in a particular segment *)
     fun numBindings(seg,[]) = 0
       | numBindings(seg,(_,_,bseg,_)::t) = (if seg = bseg then 1 else 0) + numBindings(seg,t)

     (* This is the code generation for the compiler *)

     exception Unimplemented; 
  
     (* codegen takes an AST node, the output file, a list of bindings, and the class name *)
     fun codegen(class'(id,classVars,subroutines),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile class named "^id^"\n");
	  let val bindingsNew = createClassBindings(classVars)
	  in
	      codegenlist(subroutines,outFile,bindingsNew@bindings,id)
	  end)

       | codegen(constructor'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile constructor named "^id^"\n");

	  
	  	  let val bindingsNew = createLocalBindings(vardecs)
		  val bindingsP = createParamBindings(params, 0) (*check again*)
		  val newBindings = bindingsNew@bindings
		  val numVar = numBindings("local", bindings)
				val numFields = numBindings("this", bindings)
	  in
			TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(numVar)^"\n");
			TextIO.output(outFile,"push constant "^Int.toString(numFields)^"\n");
			TextIO.output(outFile,"call Memory.alloc 1\n"); (*not sure about this*)
			TextIO.output(outFile,"pop pointer 0\n");
	      codegenlist(statements,outFile,bindingsP@newBindings,className)
	  end
	  
	  (*codegenlist(vardecs,outFile,bindings,className);*)
	  )
	 
       | codegen(function'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile function named "^id^"\n");

	  
	  	  let val bindingsNew = createLocalBindings(vardecs)
		  val bindingsP = createParamBindings(params, 0) (*check again*)
		  val newBindings = bindingsNew@bindings
				val i = numBindings("local", bindingsP@newBindings)
	  in
			TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(i)^"\n");
	      codegenlist(statements,outFile,bindingsP@newBindings,className)
	  end
	  
	  (*codegenlist(vardecs,outFile,bindings,className);*)
	  )

       | codegen(method'(typ,id,params,(vardecs,statements)),outFile,bindings,className) =
	 
	 (TextIO.output(TextIO.stdOut, "Attempt to compile method named "^id^"\n");

	  
	  	  let val bindingsNew = createLocalBindings(vardecs)
		  val bindingsP = createParamBindings(params, numBindings("argument", bindings)+1) (*check again*)
		  val newBindings = bindingsNew@bindings
				val i = numBindings("local", bindingsP@newBindings)
	  in
			TextIO.output(outFile,"function "^className^"."^id^" "^Int.toString(i)^"\n");
			TextIO.output(outFile,"push argument 0\n"); (*not sure*)
			TextIO.output(outFile,"pop pointer 0\n");
	      codegenlist(statements,outFile,bindingsP@newBindings,className)
	  end
	  
	  (*codegenlist(vardecs,outFile,bindings,className);*)
	  )	 
       | codegen(this',outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile this\n");
		TextIO.output(outFile, "push pointer 0\n")
)

       | codegen(null',outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile this\n");
		TextIO.output(outFile, "push constant 0\n")
)





       | codegen(string'(s),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to compile string\n");
		TextIO.output(outFile, "push constant "^Int.toString(size s)^"\n");
		TextIO.output(outFile, "call String.new 1\n");
		TextIO.output(outFile, printC(String.explode(s)))
		

		(*allPrintC s outFile*)

			
)
	


	
	 | codegen(do'(call),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call a subroutine with a do statement\n");
	 codegen(call,outFile,bindings,className);
	 TextIO.output(outFile, "pop temp 0\n"))
	 
	 (*NEED TO CHANGE LETVAL'*)
	 (*probably do something with bindings*)
	 | codegen(letval'(id, expr),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call letval\n");
	 codegen(expr,outFile,bindings,className);
         let    
			val (typ, seg, offS) = boundTo(id, bindings)	 
			in
	TextIO.output(outFile,"pop "^seg^" "^Int.toString(offS)^ "\n") (*use bindings rather than hardcode*)
	end
	(*TextIO.output(outFile,"push local 0\n")*))

	 | codegen(letarray'(id, expr1, expr2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to letarray\n");
	 codegen(expr1,outFile,bindings,className);
         let    
			val (typ, seg, offS) = boundTo(id, bindings)	 
			in
	TextIO.output(outFile,"push "^seg^" "^Int.toString(offS)^"\n");
	TextIO.output(outFile,"add\n");
	codegen(expr2,outFile,bindings,className);
	TextIO.output(outFile,"pop temp 0\n");
	TextIO.output(outFile,"pop pointer 1\n");
	TextIO.output(outFile,"push temp 0\n");
	TextIO.output(outFile,"pop that 0\n")
	end
	(*TextIO.output(outFile,"push local 0\n")*))





	
	 | codegen(while'(expr, statementL),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt while\n");
	 let val l = nextLabel()
	 val lEnd = nextLabel()
	 in
	 TextIO.output(outFile, "label "^ l^"\n");
	 codegen(expr,outFile,bindings,className);
	 TextIO.output(outFile, "not\n");
	 TextIO.output(outFile, "if-goto "^lEnd^"\n");
	 codegenlist(statementL,outFile,bindings,className);
	 TextIO.output(outFile, "goto "^ l^"\n");
	 TextIO.output(outFile, "label "^ lEnd^"\n")
	 end
	 )		
	
	
	 
	 
	 
	 | codegen(subcallq'(id1,id2,exprlist),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call "^id1^"."^id2^"\n");
		
         let    
			val (typ, seg, offS) = boundTo(id1, bindings)
			val myL = length exprlist
			in	
		TextIO.output(outFile, "push "^seg^" "^ Int.toString(offS)^"\n");
		codegenlist(exprlist,outFile,bindings,className);
		TextIO.output(outFile, "call "^typ^"."^id2^" "^Int.toString(myL +1)^"\n")
			end	
		handle unboundId =>  
		(codegenlist(exprlist,outFile,bindings,className);
		TextIO.output(outFile, "call "^id1^"."^id2^" "^Int.toString(length exprlist)^"\n"))
		)
	 | codegen(subcall'(id1,exprlist),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call "^id1^"\n");
		
         let    
			val myL = length exprlist
			in	
		TextIO.output(outFile, "push pointer 0\n");
		codegenlist(exprlist,outFile,bindings,className);
		TextIO.output(outFile, "call "^className^"."^id1^" "^Int.toString(myL +1)^"\n")
			end	
		)		
		
	 | codegen(id'(id1),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt id\n");
         let    
			val (typ, seg, offS) = boundTo(id1, bindings)	 
			in
	TextIO.output(outFile,"push "^seg^" "^Int.toString(offS)^ "\n") (*use bindings rather than hardcode*)
	end)		(*MAKE USE OF BINDINGS*)



	 | codegen(idarray'(id1, expr),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt idarray\n");
	 codegen(expr,outFile,bindings,className);
         let    
			val (typ, seg, offS) = boundTo(id1, bindings)	 
			in
	TextIO.output(outFile,"push "^seg^" "^Int.toString(offS)^ "\n"); (*use bindings rather than hardcode*)
	TextIO.output(outFile, "add\n");
	 TextIO.output(outFile, "pop pointer 1\n");
	 TextIO.output(outFile, "push that 0\n")  (*continue to handle idarray*)
	 end
)	

 
	 | codegen(true',outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt true\n");
	 TextIO.output(outFile, "push constant 0\n");
	 TextIO.output(outFile, "not\n") (*check again*)
		)	
	 | codegen(false',outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt false\n");
	 TextIO.output(outFile, "push constant 0\n")
 (*check again*)
		)	
(*HANDLE IF*)		
	 | codegen(ifelse'(expr, st1, st2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt ifelse\n");	 
	 let val l = nextLabel()
	 val lF = nextLabel()
	 val lEnd = nextLabel()

	 in
	 codegen(expr,outFile,bindings,className);
	 TextIO.output(outFile, "if-goto "^l^"\n");
	 TextIO.output(outFile, "goto "^lF^"\n");
	 TextIO.output(outFile, "label "^l^"\n");
	 codegenlist(st1,outFile,bindings,className);
	 TextIO.output(outFile, "goto "^lEnd^"\n");
	 TextIO.output(outFile, "label "^lF^"\n");
	 codegenlist(st2,outFile,bindings,className);
	 TextIO.output(outFile, "label "^lEnd^"\n")	 
	end
		)

	 | codegen(if'(expr, st1),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt if\n");	 
	 let val l = nextLabel()
	 val lF = nextLabel()

	 in
	 codegen(expr,outFile,bindings,className);
	 TextIO.output(outFile, "if-goto "^l^"\n");
	 TextIO.output(outFile, "goto "^lF^"\n");
	 TextIO.output(outFile, "label "^l^"\n");
	 codegenlist(st1,outFile,bindings,className);
	 TextIO.output(outFile, "label "^lF^"\n")
	end
		)

		

	 | codegen(gt'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt gt\n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "gt\n"))
		
	 | codegen(lt'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt lt\n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "lt\n"))		
		
	 | codegen(and'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt and\n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "and\n"))
		
	 | codegen(or'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt and\n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "or\n"))		
		
		
	 | codegen(equal'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt eq\n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "eq\n"))

	 | codegen(not'(t),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt not\n");
		codegen(t, outFile,bindings,className);
		TextIO.output(outFile, "not\n"))



	 
	 | codegen(returnvoid',outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt returnvoid statement\n");
		TextIO.output(outFile, "push constant 0\nreturn\n"))
		
	 | codegen(return'(expr),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt return statement\n");
		codegen(expr, outFile,bindings,className);
		TextIO.output(outFile, "return\n"))		
		
		
	| codegen(integer'(i),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call integer "^Int.toString(i)^"\n");
		TextIO.output(outFile, "push constant "^Int.toString(i)^"\n"))	
	| codegen(add'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call add \n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "add\n"))	

	| codegen(sub'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call sub \n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);
		TextIO.output(outFile, "sub\n"))


		
	| codegen(negate'(t),outFile,bindings,className) =	
	 (TextIO.output(TextIO.stdOut, "Attempt to call negate \n");
		codegen(t, outFile,bindings,className);	
		TextIO.output(outFile, "neg\n"))
	
	
	| codegen(prod'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call multiply \n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);	 
		TextIO.output(outFile, "call Math.multiply 2\n"))	

	| codegen(div'(t1, t2),outFile,bindings,className) =
	 (TextIO.output(TextIO.stdOut, "Attempt to call divide \n");
		codegen(t1, outFile,bindings,className);
		codegen(t2, outFile,bindings,className);	 
		TextIO.output(outFile, "call Math.divide 2\n"))	
	
       (*| codegen(_,outFile,bindings,className) =
         (TextIO.output(TextIO.stdOut, "Attempt to compile expression not currently supported!\n");
          raise Unimplemented) *)

     and codegenlist([],outFile,bindings,className) = ()
       | codegenlist(h::t,outFile,bindings,className) =
	 (codegen(h,outFile,bindings,className);
	  codegenlist(t,outFile,bindings,className))

     fun compile filename  = 
         let val (ast, _) = jackparse filename
	     val fileName = hd (String.tokens (fn c => c = #".") filename)
             val outFile = TextIO.openOut(fileName^".vm")
         in
           let val _ = codegen(ast,outFile,[],"")
           in 
             TextIO.closeOut(outFile)
           end
         end 
         handle _ => (TextIO.output(TextIO.stdOut, "An error occurred while compiling!\n\n")); 
             
       
     fun run(a,b::c) = (compile b; OS.Process.success)
       | run(a,b) = (TextIO.print("usage: sml @SMLload=jack\n");
                     OS.Process.success)
end


