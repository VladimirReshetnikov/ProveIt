function Code(el)
  local choices = {'|','!',';','@',':'}
  for _,d in ipairs(choices) do
    if not string.find(el.text,d,1,true) then
      return pandoc.RawInline('latex','\\path'..d..el.text..d)
    end
  end
  return el
end
