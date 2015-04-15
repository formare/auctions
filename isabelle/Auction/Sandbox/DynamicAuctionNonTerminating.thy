theory DynamicAuctionNonTerminating
imports

t
"~~/src/afp/Coinductive/Coinductive_List"
"~~/src/HOL/Library/Code_Numeral"
"~~/src/HOL/Library/Code_Char"

begin

(* In the following we use a simple example of a static auction, which can be replaced by a more
   sophisticated one. Here it just prints the current state of the auction after each input bid. 
   The print is done by the messageAfterEachBid which is applied after the bid has been added
   to the end of the flat bid list l. E.g., for "l0 == [5, 3, 1, 1, 2, 2, 3, 4, 4, 6]" 
   staticAuction will put first the 5 to the end of the list and then return the message
   "(STR ''Current winner: [1]\<newline>Liveliness: [True, True, True, True]\<newline>Next, input bid for round 3,
         participant 0'',  [3, 1, 1, 2, 2, 3, 4, 4, 6, 5])" :: "String.literal \<times> integer list"
   which will be used in the Scala code."
   *)
abbreviation "staticAuction == 
             (%l. (String.implode(messageAfterEachBid (map nat_of_integer l)), 
                  l)) 
             o (
             %l. (tl l) @ [hd l])"

(* The dynamic auction is defined as an iteration of output, staticAuction, and input, where the
   output and input are written in Scala and essentially are assumed to be the identity, except
   for the side effects of printing the message of staticAuction and reading in the next bid,
   respectively. *)
abbreviation "dynamicAuctionNonTerminating input output == 
   iterates (output o staticAuction o input) []"
end

