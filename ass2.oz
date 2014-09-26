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
   local Condition in
      case X
      of ident(Var) then
	 Condition = {RetrieveFromSAS Env.Var}
      else
	 Condition = X
      end
      if Condition == literal(true) then
	 {Push semstate(statement:S1 environment:Env)}
      else
	 if Condition == literal(false) then
	    {Push semstate(statement:S2 environment:Env)}
	 else
	    raise illFormedStatement(X) end
	 end
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
	 case '#'(FormalParams ActualParams)
	 of nil#nil then CalleeEnv
	 [] '#'(ident(Var)|Formalr ident(Actual)|Actualr) then
	    local NewEnv in
	       {AdjoinAt CalleeEnv Var {AddKeyToSas} NewEnv}
	       {Unify ident(Var) {RetrieveFromSAS CallerEnv.Actual} NewEnv}
	       {DeclareBind Formalr Actualr NewEnv CallerEnv}
	    end
	 [] '#'(ident(Var)|Formalr Actual|Actualr) then
	    local NewEnv in
	       {AdjoinAt CalleeEnv Var {AddKeyToSas} NewEnv}
	       {Unify ident(Var) Actual NewEnv}
	       {DeclareBind Formalr Actualr NewEnv CallerEnv}
	    end
	 else
	    raise wrongArityException(ActualParams FormalParams) end
	 end
      end
      Procedure = {RetrieveFromSAS Env.X}
      NewEnv = {DeclareBind Procedure.argument Args Procedure.environment Env}
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
	    [] apply|ident(X)|Args then
	       {ApplyProc X Args @Tmp.environment}
	       {Recurse}
	    [] X|Xr then
	       if Xr \= nil then
		  {Push semstate(statement:Xr environment:@Tmp.environment)}
	       else skip
	       end
	       {Push semstate(statement:X environment:@Tmp.environment)}
	       {Recurse}
	    end
	 else {Browse 'Done!'}
	 end
      end
      {Recurse} 
   end
end

%{Interpret [[nop] [nop] [nop]]}

{Interpret [
	    [localvar ident(x)
	     [localvar ident(y)
	      [localvar ident(z)
	       [
		[nop]
		[bind ident(y) literal(a)]
		%[bind ident(x) [record ident(y) [[literal(f1) literal(a)] [ident(y) literal(v1)]]]]
		%[conditional ident(y) [bind ident(z) literal(true)] [bind ident(z) literal(false)]]
		%[match ident(x) [record literal(a) [[literal(f1) ident(y)] [literal(a) literal(v2)]]] [nop] [bind ident(z) literal(false)]]
		[bind ident(x) [procedure [ident(a) ident(b)] [[bind ident(b) literal(procedure)] [nop]]]]
		[apply ident(x) literal(1) literal(procedure)]
	       ]
	      ]
	     ]
	    ]
	   ]}

%{Interpret [[localvar ident(x)
%	[[nop]  [localvar ident(y)[[bind ident(x) ident(y)] [localvar ident(x)[nop]]]]]]]}

%{Interpret [[localvar ident(x)[localvar ident(y)[[bind ident(x) [record literal(a)
%[[literal(feature1) literal(10)]]]]]]]]}


local A B C in
   A = [1 2 3]
   B = [a b c]
   case '#'(A B)
   of '#'(X|Xr Y|Yr) then
      {Browse X}
      {Browse Y}
   end
end
