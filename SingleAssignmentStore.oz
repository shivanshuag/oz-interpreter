declare

SasIndex = {NewCell 0}
Sas = {Dictionary.new}

fun {RetrieveFromSAS X}
   {Dictionary.get Sas X}
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

