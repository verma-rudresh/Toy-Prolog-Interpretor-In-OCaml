
type symbol = S of string * int;;
type variable = string;;
type term = V of variable | Node of symbol * (term list);;
type substitution = Q of term * term;;
type clause = term * term list;;
