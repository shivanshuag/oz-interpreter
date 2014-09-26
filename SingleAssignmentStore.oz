declare

SasIndex = {NewCell 0}
Sas = {Dictionary.new}

fun {RetrieveFromSAS X}
   local Value in
      Value = {Dictionary.get Sas X}
      case Value
      of refrence(Key) then {RetrieveFromSAS Key}
      else
	 Value
      end
   end
end

proc {BindRefToKeyInSAS Key RefKey}
   {Dictionary.remove Sas Key}
   {Dictionary.put Sas Key refrence(RefKey)}
end

proc {BindValueToKeyInSAS Key Val}
   {Dictionary.remove Sas Key}
   {Dictionary.put Sas Key Val}
end

fun {AddKeyToSas}
   SasIndex := @SasIndex + 1
   {Dictionary.put Sas @SasIndex equivalence(@SasIndex)}
   @SasIndex
end

