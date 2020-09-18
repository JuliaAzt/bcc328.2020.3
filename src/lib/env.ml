(* env.ml *)

module S = Symbol
module T = Type

type entry =
  | VarEntry of T.ty
  | FunEntry of T.ty list * T.ty
  [@@deriving show]

let standard_types =
  [ ("void", T.VOID )
  ; ("bool", T.BOOL )
  ; ("int", T.INT)
  ; ("real", T.REAL)
  ; ("string", T.STRING)
  ]

let standard_functions =
  [ "printbool", [T.BOOL], T.VOID
  ; "not", [T.BOOL], T.BOOL
  ]

let base_tenv =
  List.fold_left
    (fun env (name, t) -> S.enter (S.symbol name) t env)
    S.empty
    standard_types

let base_venv =
  List.fold_left
    (fun env (name, formals, result) ->
      S.enter
        (S.symbol name)
        (FunEntry (formals, result))
        env)
    S.empty
    standard_functions

type env =
  { tenv: T.ty Symbol.table;
    venv: entry Symbol.table;
    inloop: bool
  }

let initial =
  { tenv = base_tenv;
    venv = base_venv;
    inloop = false;
  }
