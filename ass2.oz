\insert Unify.oz

declare SemStack Push1 Pop Print Interpret Tmp AddLocal

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

proc {AddLocal X Env Statement}
   local NewEnv in
      {AdjoinAt Env X {AddKeyToSas} NewEnv}
      {Push semstate(statement:Statement environment:NewEnv)}
      %{Browse {RetrieveFromSAS {AddKeyToSas}}}
   end
end   

proc {HandleCondition X S1 S2 Env}
   if {RetrieveFromSAS Env.X} then
      {Push semstate(statement:S1 environment:Env)}
   else
      {Push semstate(statement:S2 environment:Env)}
   end
end

proc {HandleCase X Pattern S1 S2 Env}
   
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
	       {Unify X Y @Tmp.environment}
	       {Recurse}
	    [] [conditional X S1 S2] then
	       {HandleCondition X S1 S2 @Tmp.environment}
	       {Recurse}
	    [] [match X Pattern S1 S2] then
	       {HandleCase X Pattern S1 S2 @tmp.environment}
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
%{Interpret [[localvar ident(x)
%	    [localvar ident(y)
%	     [localvar ident(x)
%	      [nop]]]]]}

%{Interpret [[localvar ident(x)
%	[[nop]  [localvar ident(y)[[bind ident(x) ident(y)] [localvar ident(x)[nop]]]]]]]}

%{Interpret [[localvar ident(x)[localvar ident(y)[[bind ident(x) [record literal(a)
%[[literal(feature1) literal(10)]]]]]]]]}

