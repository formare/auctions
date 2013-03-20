sed '/^ *::{/,/^ *::}/ d'| sed '1,/^ *begin/ d'  | sed -n '/^ *begin/,/^::\$EOF/ p' | sed '/^..*$/,/^$/ !d'
# Ugly Unix shell script (should work with most shells: Bourne, rc, csh, etc...):  
# -removes proofs (not robustly, assuming source provides them explicitly wrapped in special comment lines ::{, ::}!)
# -removes first section (begin ... begin)
# -squeezes contiguous empty lines into one

