(* comment *)
(*
 * multiline
 * (* nested comment *)
 *)

let f x = int_of_float ((float_of_int x) +. 3.4)

let rec r n = 1 + if n>0 then (n + (r (n-1))) else 3

let () = let a = 7 in print_endline (string_of_int (r (let a = f a in f a)))
