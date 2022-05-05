(* Abstract Syntax Tree *)

type variable = string
type aexpr = Num of int | Var of string | Minus of aexpr * aexpr
type bexpr = Lt of aexpr * aexpr | Nand of bexpr * bexpr
type 'a tree = 
  | Emptystmt of 'a
  | Break of 'a
  | Assign of variable * aexpr * 'a
  | If of bexpr * 'a tree * 'a
  | Ifelse of bexpr * 'a tree * 'a tree * 'a
  | While of bexpr * 'a tree * 'a
  | Stmtlist of 'a tree list * 'a
  | Prog of 'a tree * 'a


type label = int
type lprog = label tree


(* 
   Associates to each program point a unique (integer) label starting from 1.
   Loses the information associated to every node.
*)
let labelize (p : 'a tree) : lprog =
  let new_label =
    let cpt = ref (-1) in
    fun () -> incr cpt ; !cpt
  in
  let rec mklabel = function
    | Prog (t, info) -> Prog (mklabel t,  new_label ())
    | Assign (id, ae, info) -> Assign (id, ae, new_label ())
    | Ifelse (cond, then_, else_, info) ->
        let block_then = mklabel then_ in
        let block_else = mklabel else_ in
        let lab = new_label () in
        Ifelse (cond, block_then, block_else, lab)
    | While (cond, body, info) ->
        let lab = new_label () in
        let body = mklabel body in
        While (cond, body, lab)
    | If (cond, then_, info) ->
        let lab = new_label () in
        let bthen_ = mklabel then_ in
        If (cond, bthen_, lab)
    | Stmtlist (list, info) -> 
        let lab = new_label () in
        Stmtlist (List.map mklabel list, lab)
    | Emptystmt info -> Emptystmt (new_label ())
    | Break info -> Break (new_label ())
  in
  mklabel p
