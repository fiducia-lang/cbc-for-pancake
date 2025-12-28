(*
  Abstract syntax for Pancake language.
  Pancake is an imperative language with
  instructions for conditionals, While loop,
  memory load and store, functions,
  and foreign function calls.
*)
Theory panReducedLang
Ancestors
  mlstring
  asm (* for binop and cmp *)
  backend_common  (* for overloading the shift operation *)
Libs
  preamble


(* for overloading the shift operation *)

Type shift = ``:ast$shift``

Type sname = ``:mlstring``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type eid     = ``:mlstring``

Type decname = ``:mlstring``

Type index = ``:num``

Datatype:
  shape = One
        | Comb (shape list)
End

Datatype:
  panop = (* Div | *)Mul (* | Mod*)
End

Datatype:
  varkind = Local | Global
End

Datatype:
  exp = Const ('a word)
      | Var varkind varname
      | Struct (exp list)
      | Field index exp
      | Load shape exp (* exp: start addr of value with given shape *)
      | Load32 exp
      | LoadByte exp
      | Op binop (exp list)
      | Panop panop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
      | BaseAddr
      | TopAddr
      | BytesInWord
End

Datatype:
  opsize = Op8 | OpW | Op32 | Op16
End

Datatype:
  prog = Skip
       | Dec varname shape ('a exp) prog
       | Assign varkind varname ('a exp)  (* dest, source *)
       | Store     ('a exp) ('a exp) (* dest, source *)
       | Store32   ('a exp) ('a exp) (* dest, source *)
       | StoreByte ('a exp) ('a exp) (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Raise eid ('a exp)
       | Return ('a exp)
       | Annot mlstring mlstring
End

Theorem MEM_IMP_shape_size:
   !shapes a. MEM a shapes ==> (shape_size a < 1 + shape1_size shapes)
Proof
  Induct >> fs [] >>
  rpt strip_tac >> rw [fetch "-" "shape_size_def"] >>
  res_tac >> decide_tac
QED

Definition size_of_shape_def:
  size_of_shape One = 1 /\
  size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)
Termination
  wf_rel_tac `measure shape_size` >>
  fs [MEM_IMP_shape_size]
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End

Definition with_shape_def:
  (with_shape [] _ = []) ∧
  (with_shape (sh::shs) e =
     TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))
End

Definition exp_ids_def:
  (exp_ids Skip = ([]:mlstring list)) ∧
  (exp_ids (Raise e _) = [e]) ∧
  (exp_ids (Dec _ _ _ p) = exp_ids p) ∧
  (exp_ids (Seq p q) = exp_ids p ++ exp_ids q) ∧
  (exp_ids (If _ p q) = exp_ids p ++ exp_ids q) ∧
  (exp_ids (While _ p) = exp_ids p) ∧
  (exp_ids _ = [])
End

Definition var_exp_def:
  (var_exp (Const w) = ([]:mlstring list)) ∧
  (var_exp (Var Local v) = [v]) ∧
  (var_exp (Var Global v) = []) ∧
  (var_exp (Struct es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Field i e) = var_exp e) ∧
  (var_exp (Load sh e) = var_exp e) ∧
  (var_exp (Load32 e) = var_exp e) ∧
  (var_exp (LoadByte e) = var_exp e) ∧
  (var_exp (Op bop es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Panop op es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Cmp c e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (var_exp (Shift sh e num) = var_exp e) ∧
  (var_exp BaseAddr = []) ∧
  (var_exp TopAddr = []) ∧
  (var_exp BytesInWord = [])
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition global_var_exp_def:
  (global_var_exp (Const w) = ([]:mlstring list)) ∧
  (global_var_exp (Var Local v) = []) ∧
  (global_var_exp (Var Global v) = [v]) ∧
  (global_var_exp (Struct es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Field i e) = global_var_exp e) ∧
  (global_var_exp (Load sh e) = global_var_exp e) ∧
  (global_var_exp (LoadByte e) = global_var_exp e) ∧
  (global_var_exp (Op bop es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Panop op es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Cmp c e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_exp (Shift sh e num) = global_var_exp e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition load_op_def:
  load_op Op8 = Load8 ∧
  load_op Op16 = Load16 ∧
  load_op OpW = Load ∧
  load_op Op32 = Load32
End

Definition store_op_def:
  store_op Op8 = Store8 ∧
  store_op Op16 = Store16 ∧
  store_op OpW = Store ∧
  store_op Op32 = Store32
End
