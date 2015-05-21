theory Chores1

imports Main "./VCG/Argmax"


begin

text {* bidVector is a list of list. Each inner list contains the bids of a single participant, 
and is made of True/False corresponding to single tasks (this is an on/off auction round). *}

term transpose

abbreviation "candidatesForTask n bidVector == (transpose (bidVector))!n"

abbreviation "winnerOfTask n bidVector random == candidatesForTask n bidVector ! random"

end
