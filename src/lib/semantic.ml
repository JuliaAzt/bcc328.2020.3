(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value

(* Checking expressions *)
let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) -> check_exp_let env pos tref decs body
  | A.VarExp v -> check_var env v tref
  | A.AssignExp (v, e) -> let t1 = check_var env v tref in
                          let t2 = check_exp env e in
                          compatible t1 t2 pos;
                          T.VOID
  | A.IfExp (t,b,v) ->  let ty1 = check_exp env t in
                        let ty2 = check_exp env b in
                        begin
                          match ty1 with 
                          | T.BOOL -> begin
                            match v with   
                            |Some v1 -> compatible ty2 (check_exp env v1) pos;
                                        set tref ty2
                            |None -> set tref T.VOID
                            end
                          | _ -> type_mismatch pos (T.BOOL) ty1
                        end
  | A.BinaryExp (l,op,r)->  begin
                              match op with
                              | A.And | A.Or -> check_logic_types env l r pos tref
                              | A.Equal | A.NotEqual -> check_equal_notequal_types env l r pos tref
                              | A.GreaterThan | A.GreaterEqual | A.LowerThan | A.LowerEqual -> check_compare_types env l r pos tref
                              | A.Plus | A.Minus | A.Div | A.Times | A.Mod | A.Power -> check_operation_types env l r pos tref
                              |_ -> Error.fatal "unimplemented"
                            end
                          
  | A.WhileExp (c,e) -> let t1 = check_exp env c in
                        let env = {env with inloop = true} in
                        begin
                          match t1 with
                          |T.BOOL -> ignore(check_exp env e);  
                                     set tref T.VOID
                          | _ -> type_mismatch pos (T.BOOL) t1
                        end 
  | A.BreakExp -> if(env.inloop == true) then set tref T.VOID else Error.fatal "Break outside loop"
  | A.NegativeExp e -> let t1 = check_exp env e in
                        begin
                          match t1 with
                          |T.REAL -> set tref T.REAL
                          |T.INT -> set tref T.INT
                          | _ -> Error.fatal "Expected types real or integer"
                        end
  | A.ExpSeq ls -> avaluate_seq env pos ls tref

  | _ -> Error.fatal "unimplemented"

and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

and check_logic_types  env l r pos tref = 
  let t1 = check_exp env l in
  let t2 = check_exp env r in
  match (t1,t2) with
  | T.BOOL, T.BOOL -> set tref T.BOOL
  | T.BOOL, t2 -> type_mismatch pos (T.BOOL) t2
  | t1, T.BOOL -> type_mismatch pos (T.BOOL) t1
  |_ -> Error.fatal "type mismatch expected bool"

and check_compare_types  env l r pos tref = 
  let t1 = check_exp env l in
  let t2 = check_exp env r in
  match (t1,t2) with
  | T.INT, T.INT | T.STRING, T.STRING | T.REAL, T.REAL -> set tref T.BOOL
  |_ -> Error.fatal "type mismatch"

and check_operation_types env l r pos tref =
  let t1 = check_exp env l in
  let t2 = check_exp env r in
  match (t1,t2) with
  | T.INT, T.INT -> set tref T.INT
  | T.INT, T.REAL | T.REAL, T.INT| T.REAL, T.REAL -> set tref T.REAL
  |_ -> Error.fatal "type mismatch"

and check_equal_notequal_types  env l r pos tref =
  let t1 = check_exp env l in
  let t2 = check_exp env r in
  compatible t1 t2 pos;
  set tref T.BOOL


and avaluate_seq env pos ls tref =
  let rec aux env pos ls tref=  
    match ls with
    | [] -> set tref T.VOID
    | h::[] -> set tref (check_exp env h)
    | h::t-> aux env pos t tref
  in aux env pos ls tref;
  
and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | _ -> Error.fatal "unimplemented"

and check_var env (pos, v) tref =
  match v with
  | A.SimpleVar v -> (let r = varlook env.venv v pos in set tref r)
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
