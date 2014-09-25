\insert Unify.oz

declare SemStack Push1 Pop Print Interpret Tmp AddLocal DeclareVars

SemStack = {NewCell nil}
Tmp = {NewCell nil}

proc {Print}
   {Browse @SemStack}
   {Browse {Dictionary.toRecord singleAssStore Sas}}
end   

proc {Push S}
   SemStack := S|@SemStack
end

fun {Pop}
   case @SemStack
   of nil then nil
   [] S1|S2 then
      SemStack := S2
      S1
   end
end

proc {HandleBind X Y Env}
   case Y
   of [procedure Args Statements] then
      {Unify X procedure(argument:Args statement:Statements environment:Env) Env}
   else {Unify X Y Env}
   end
end

proc {AddLocal X Env Statement}
   local NewEnv in
      {AdjoinAt Env X {AddKeyToSas} NewEnv}
      {Push semstate(statement:Statement environment:NewEnv)}
   end
end   

proc {HandleCondition X S1 S2 Env}
   if {RetrieveFromSAS Env.X} == literal(true) then
      {Push semstate(statement:S1 environment:Env)}
   else
      if {RetrieveFromSAS Env.X} == literal(false) then
	 {Push semstate(statement:S2 environment:Env)}
      else
	 raise illFormedStatement(X) end
      end
   end
end

%local DeclareVars Pattern in
fun {DeclareVars Pattern Env}
   case Pattern
   of [record RecordName Features] then
      local IterList NewEnv in
	 NewEnv = {DeclareVars RecordName Env}
	 fun {IterList List Env}
	    case List
	    of nil then Env
	    [] Feat|FeatR then
	       local ThisEnv in
		  ThisEnv = {DeclareVars Feat.2.1 {DeclareVars Feat.1 Env}}
		  {IterList FeatR ThisEnv}
	       end
	    end
	 end
	 {IterList Features NewEnv}
      end
   [] ident(Variable) then
      local NewEnv in
	 {AdjoinAt Env Variable {AddKeyToSas} NewEnv}
	 NewEnv
      end
   else
      Env
   end
end
%   Pattern = [record ident(x) [[literal(f1) ident(y)] [ident(z) [record literal(abc) [[literal(f3) ident(k)]]]] [literal(k) literal(sajk)]  ]]
%   {Browse {DeclareVars Pattern env()}}
%end

proc {HandleCase X Pattern S1 S2 Env}
   try
      local NewEnv in
	 NewEnv = {DeclareVars Pattern Env}
	 {Unify X Pattern NewEnv}
	 {Push semstate(statement:S1 environment:NewEnv)}
      end
   catch incompatibleTypes(X Y) then
      {Push semstate(statement:S2 environment:Env)}
   end
end

proc {ApplyProc X Args Env}
   local DeclareBind NewEnv Procedure in
      fun {DeclareBind FormalParams ActualParams CalleeEnv CallerEnv}
	 case FormalParams#ActualParams
	 of nil#nil then CalleeEnv
	 [] ident(Var)|Formalr#Actual|Actualr then
	    local NewEnv in
	       {AdjoinAt CalleeEnv Var {AddKeyToSas} NewEnv}
	       {Unify ident(Var) {RetrieveFromSAS CallerEnv.Actual} NewEnv}
	       {DeclareBind Formalr Actualr NewEnv CallerEnv}
	    end
	 else
	    raise wrongArityException(ActualParams FormalParams) end
	 end
      end
      Procedure = {RetrieveFromSAS Env.X}
      NewEnv = {DeclareBind Procedure.arguments Args Procedure.environment Env}
      {Push semstate(statement:Procedure.statement environment:NewEnv)}
   end
end

proc {Interpret AST}
   {Push semstate(statement:AST environment:env())}
   local Recurse in
      proc {Recurse}
	 {Print}
	 Tmp := {Pop}
	 if @Tmp \= nil then
	    case @Tmp.statement
	    of nil then {Browse 'Done!'}
	    [] [nop] then {Recurse}
	    [] [localvar ident(X) Xr] then
	       {AddLocal X @Tmp.environment Xr}
	       {Recurse}
	    [] [bind X Y] then
	       {HandleBind X Y @Tmp.environment}
	       {Recurse}
	    [] [conditional X S1 S2] then
	       {HandleCondition X S1 S2 @Tmp.environment}
	       {Recurse}
	    [] [match X Pattern S1 S2] then
	       {HandleCase X Pattern S1 S2 @Tmp.environment}
	       {Recurse}
	    [] apply|X|Args then
	       {ApplyProc X Args @Tmp.environment}
	       {Recurse}
	    [] X|Xr then
	       if Xr \= nil then
		  {Push semstate(statement:Xr environment:@Tmp.environment)}
	       else skip
	       end
	    end
	    {Recurse}
	 else {Browse 'Done!'}
	 end
      end
      {Recurse} 
   end
end

%{Interpret [[nop] [nop] [nop]]}
%{Interpret [[localvar ident(x)
%	    [localvar ident(y)
%	     [localvar ident(x)
%	      [nop]]]]]}

%{Interpret [[localvar ident(x)
%	[[nop]  [localvar ident(y)[[bind ident(x) ident(y)] [localvar ident(x)[nop]]]]]]]}

%{Interpret [[localvar ident(x)[localvar ident(y)[[bind ident(x) [record literal(a)
%[[literal(feature1) literal(10)]]]]]]]]}

