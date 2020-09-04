(* NAME: RUDRESH RAJ VERMA *)
(* ASSIGNMENT 6 *)
open Types
exception SuspendedHere

open Printf

(* initializer for solving query function *)
let init:bool*substitution list = (false,[]);;

(* function to find whether a symbol has already appeared in list or not *)
let rec find_in_list (sym_list) (sym) = match sym_list with
| h::t -> if(h=sym) then true else find_in_list t sym
| [] -> false;;

(* Helper function to check whether a signature is valid or not *)
let rec helper_check_sig (sig_list) (sym_list) = match sig_list with
| [] -> true
| h::t -> let (sym,arity) = h in 
          if(arity < 0) then false
          else 
            if(find_in_list sym_list sym) then false 
            else (helper_check_sig t (sym::sym_list))
          ;;
  
(* main function to check whether a signature is valid or not *)
let check_sig (sig_list) = helper_check_sig (sig_list) [];;

(* function to find arity of a symbol *)
let rec find_arity sig_list my_sym = match sig_list with
| h::t -> let (sym,arity) = h in
          if (sym = my_sym) then arity 
          else find_arity t my_sym;
| [] -> -1;;


(* function to find the size of a list *)
let rec size_of_list my_list = match my_list with
| h::t -> 1 + size_of_list t
| [] -> 0;;

(* Function to check whether a given pre-term is valid or not *)
let rec wfterm my_term sig_list = match my_term with
| V(var) -> true
| Node(S(sym,arity), term_list) -> if(arity != size_of_list term_list) then false else 
	match term_list with
	| [] -> true
	| _ -> wfterm_list term_list sig_list;
and wfterm_list termList sig_list = match termList with
| [] -> true
| h::t -> (wfterm h sig_list) && (wfterm_list t sig_list);;

(* Function to find the maximum of two numbers *)
let max a b = if a<b then b else a;;


(* helper function to find the list of variables with no repetition in a pre-term *)
let rec helper_vars myTerm varsList = match myTerm with
| V(var) -> if((find_in_list varsList myTerm) = false) then myTerm::varsList else varsList;
| Node(S(sym, arity), term_list) -> match term_list with
	| [] -> varsList
	| _ -> varsOfTermList term_list varsList;
and varsOfTermList termList varsList = match termList with
| [] -> varsList
| h::t -> varsOfTermList t (helper_vars h varsList);;
(* main function to find the list of variables in a pre-term *)
let vars myTerm = helper_vars myTerm [];;

(* function to find height of a term *)
let rec ht term = match term with Node(S(sym, arity), l) -> (1+ (List.fold_left max 0 (List.map ht l))) | V(x) -> 1;; 
(* function to find size of a term *)
let rec size term =  match term with Node(S(sym, arity), l) ->(1 + (List.fold_left (+) 0 (List.map size l))) | V(x) -> 1;;


(* function to check if a variable lies in the domain of substitution list or not *)
let rec domain substitutionList var = match substitutionList with
| h::t -> let Q(a,b) = h in
  if(a=var) then true else domain t var;
| [] -> false;;

(* given a variable, this function finds the range of that variable from the substitution list *)
let rec range substitutionList var = match substitutionList with
| h::t -> let Q(a,b) = h in
  if(a=var) then b else range t var;
| [] -> failwith "variable is not in the domain";;

(* function to find the substituted term *)
let rec subst substList myTerm  = match myTerm with
| V(var) -> if(domain substList myTerm = true) then (range substList myTerm) else myTerm
| Node(S(sym, arity), term_list) -> match term_list with
	| [] -> myTerm
	| _ -> Node(S(sym, arity), (List.map (subst substList) term_list));;

(* function to find the common elements of two lists *)
let rec intersection s1 s2 = match s2 with
| [] -> []
| x::xs -> if(find_in_list s1 x) then x::(intersection s1 xs) else intersection s1 xs;;

(* helper function to find the non common elements of two given lists *)
let rec helper_anti_intersection s1 s2 = match s1 with 
| [] -> []
| h::t -> if(find_in_list s2 h = false) then h::helper_anti_intersection t s2
          else helper_anti_intersection t s2;;

(* main function to find the non-common elements of two given lists  *)
let anti_intersection s1 s2 = helper_anti_intersection (s1@s2) (intersection s1 s2);;

(* function to find the union of two given lists *)
let unionL s1 s2 = (intersection s1 s2) @ (anti_intersection s1 s2);;

(* function to find the most general unifier of two pre-terms *)
let rec mgu t1 t2 = match t1,t2 with
| V x, V y -> if(x != y) then (true, Q(t1,t2)::[]) else (true,[])
| V x, Node(S(sym, arity), term_list) -> if(find_in_list (vars t2) t1 = false) then (true, Q(t1,t2)::[]) else (false, []);
| Node(S(sym, arity), term_list), V y -> if(find_in_list (vars t1) t2 = false) then (true, Q(t2,t1)::[]) else (false, []);
| Node(S(s1, a1), a_list), Node(S(s2, a2), b_list) -> if((s1 = s2) && (a1 = a2)) then (mgu_list a_list b_list (true, [])) else (false, []);

and mgu_list t1_list t2_list sub_list = match sub_list with 
| (true, sl) -> 
	(match (t1_list, t2_list) with
		| (x1::xs1, x2::xs2) -> (let s0 = (mgu (subst sl x1) (subst sl x2)) in
			match s0 with (true, s) -> (mgu_list xs1 xs2 (true,(List.append sl s)))
			| (false, s) ->  (false, []);
		)
		| [], _ -> (true, sl)
		| _, _ -> (false, [])
	)
| (false, sl) -> (false, []);;

(* function to unify two bool*substitution list *)
let union subList1 subList2 = match subList1, subList2 with
|	(true,s1), (true,s2) -> (true,unionL s1 s2)
|	(false,_), (true,s) -> (true,s)
|	(true,s), (false,_) -> (true,s)
| (false,_), (false,_) -> (false,[]);;

(* function to unify (term*term) list *)
let rec unify sl l = match l with
	x::xs -> unify (unifySingle (sl) x) xs
| [] -> sl
and unifySingle sl (t1, t2) = mgu_list [t1] [t2] sl;;

(* this function checks if a given Node contains the symbol "not" and is unary otherwise returns false *)
let rec checkNot term = match term with (Node(S("not",1),[li]))-> true |_-> false;;

(* this function checks if all nodes contain the symbol "not" and returns true only if all the terms satisfy the checkNot condition*)
let rec checkAllNot terms = List.fold_left (&&) true (List.map checkNot terms);;

(* function to find the size of a list *)
let rec listSize l = match l with 
	h::t -> 1 + listSize t;
| [] -> 0;;


(* let subsList = [Q((V("a")), Node(S("b", 0), []) ); Q((V("c")), Node(S("d", 0), []) )];;

let t1 = Node(S("alpha", 2), [(V "a"); Node(S("beta", 1), [(V "c")])]);;
let t2 = Node(S("alpha", 2), [Node(S("d", 0), []); Node(S("beta", 1), [Node(S("e", 0), [])])]);; *)


(* ------------------------------------------------------- *)
(* function to print the clause list, i.e. the database table *)
let rec printTerm term = match term with 
| V(var) -> printf "V(%s" var; printf "); "
| Node(S(sym, arity), termList) -> match termList with
  | [] -> printf "Node(S(%s,%d), []); " sym arity;
  | _ -> printf "Node(S(%s,%d) [" sym arity; printTermList termList; printf "]); ";
and printTermList term_list = match term_list with
| h::t ->  printTerm h; printTermList t;
| [] -> printf "";;

let rec printRow clause = match clause with 
| (term, term_list) -> printf "( "; printTerm term; printf "\n["; printTermList term_list; printf "]\n";;

let rec printTable table = match table with
| h::t -> (printRow h; printf "\n"; printTable t;)
| [] -> printf  "\n";;

(* ------------------------------------------------------- *)


let rec printTermOrg term = match term with 
| V(var) -> printf "%s" var;
| Node(S(sym, arity), termList) -> match termList with
  | [] -> printf "%s" sym;
  | _ -> printf "%s(" sym; printTermListOrg termList; printf ")";
and printTermListOrg term_list = match term_list with
| h::[] -> printTermOrg h;
| h::t ->  printTermOrg h; printf ", "; printTermListOrg t;
| [] -> printf "";;

let rec modify_subs subsList = match subsList with
	x::xs -> if(isBothSame x) then modify_subs xs else x::modify_subs xs
| [] -> []
and isBothSame subs = match subs with
Q(x,y) -> match x with V(var1) -> (match y with V(var2) -> if(var1 = var2) then true else false | _ -> false) 
					| _ -> false;;

(* function to print a node *)
let printNode node = match node with
| Node(S(sym, 0), []) -> printf "%s" sym;
| V(var) -> printf "%s" var;
|	Node(S(sym, arity), l) -> printTermOrg node;;

let rec printAnswer ans targets = match ans with
|	Q(x,y) -> match x with 
		V(var1) -> (match y with 
			V(var2) -> if(not(var1 = var2)) then (printNode x; printf " = "; printNode y; printf ",\n";)
		|	_ -> (printNode x; printf " = "; printNode y; printf ",\n";) )
	|	_ -> printf ""
and printSingleAnswer ans targets = match ans with
|	Q(x,y) -> match x with 
		V(var1) -> (match y with 
			V(var2) -> if(not(var1 = var2)) then (printNode x; printf " = "; printNode y)
		|	_ -> (printNode x; printf " = "; printNode y) )
	|	_ -> printf ""
and printAnswerList ansList targets = match ansList with
	x::[] -> (printSingleAnswer x targets;)
|	x::xs -> (printAnswer x targets; printAnswerList xs targets)
| [] -> printf "";;


let list_part env = match env with
	(bol, lst) -> lst;;
let termOfClause clause = match clause with
	(term, termList) -> term;;
let termListOfClause clause = match clause with
	(term, termList) -> termList;;

let substList subsList termList = List.map (subst subsList) termList;;

let isEmpty l = match l with [] -> true | _ -> false;;

let decideTocontinue env = 
	let rea = read_line() in
		match rea with ";" -> (printf "\n"; env)
		| "." -> (printf "TRUE\n"; raise SuspendedHere)
		| _ -> (printf "Invalid Symbol: Use only \";\" to continue and \".\" to stop!\n"; raise SuspendedHere)

(* function to get the ith element of a list *)
let rec get i l = match l with 
	x::xs -> (if (i=0) then x else get (i-1) xs)
|	[] -> failwith "List is empty";;

(* function to find the solution of a query *)
let rec eval_query gm db env targets = 
	if (isEmpty gm) then (if(isEmpty (list_part env) = false) then (printAnswerList (modify_subs (list_part env)) targets; decideTocontinue env) else env)
	else(
				match gm with 
					g1::g -> 
						(match g1 with 
							Node(S("true", 0), []) -> (eval_query g db env targets)
						| Node(S("not",1), [li]) -> (match (evaluate db li [] env targets) with 
								(true,s) -> (false,[]) | (false,s) -> eval_query g db env targets)
						| _ -> ( evaluate db g1 g env targets; ))
				| [] -> failwith "Impossible";		
			)
and evaluate db goal goalL env targets = 
	let result = ref init in
	let size = size_of_list db in
	for i=0 to (size-1) do
		let clause = get i db in
		( let (bol, sl) = mgu goal (termOfClause clause) in 
		if(bol = true) then 

		(  match (termListOfClause clause) with 
			[Node(S("true", 0), [])] -> ( let goal2 = substList sl goalL in 
				let (bol2, sl2) = (union (bol,sl) env) in 
				if(bol2 = true) then (result := union !result (eval_query goal2 db (bol2,sl2) targets))
				)
		| _ -> (let goal2 = substList sl (termListOfClause clause)@goalL in 
			let (bol2, sl2) = (union (bol,sl) env) in 
			if(bol2 = true) then result := union !result (eval_query goal2 db (bol2,sl2) targets)
			))

		)
	done;
	!result
;;