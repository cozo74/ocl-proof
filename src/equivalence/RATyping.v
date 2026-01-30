
From Stdlib Require Import String List ZArith Reals.

Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models OCLSyntax RASyntax Utils.





Definition unop_type (op : unop) (t : T_ra) : option T_ra :=
  match op, t with
  | U_Bool  _, Tra_Bool   => Some Tra_Bool

  | U_Arith UNeg,   Tra_Int  => Some Tra_Int
  | U_Arith UAbs,   Tra_Int  => Some Tra_Int
  | U_Arith UNeg,   Tra_Real => Some Tra_Real
  | U_Arith UAbs,   Tra_Real => Some Tra_Real
  | U_Arith UFloor, Tra_Real => Some Tra_Int
  | U_Arith URound, Tra_Real => Some Tra_Int

  | U_Str UToUpper, Tra_String => Some Tra_String
  | U_Str UToLower, Tra_String => Some Tra_String
  | U_Str USize,    Tra_String => Some Tra_Int

  | _, _ => None
  end.



Definition binop_type (op : binop) (t1 t2 : T_ra) : option T_ra :=
  match op, t1, t2 with
  | B_Bool  _, Tra_Bool,   Tra_Bool   => Some Tra_Bool

  (* 比较：允许 Int/Real 混合，结果 Bool；String/Object 仅限 Eq/Ne（你语义里 lt/le 不支持） *)
  | B_Comp  _, Tra_Int,    Tra_Int    => Some Tra_Bool
  | B_Comp  _, Tra_Int,    Tra_Real   => Some Tra_Bool
  | B_Comp  _, Tra_Real,   Tra_Int    => Some Tra_Bool
  | B_Comp  _, Tra_Real,   Tra_Real   => Some Tra_Bool
  | B_Comp  BEq, Tra_String, Tra_String => Some Tra_Bool
  | B_Comp  BNe, Tra_String, Tra_String => Some Tra_Bool
  | B_Comp  BEq, Tra_Object _, Tra_Object _ => Some Tra_Bool
  | B_Comp  BNe, Tra_Object _, Tra_Object _ => Some Tra_Bool

  (* 算术：Int±Real -> Real；Int op Int -> Int (但除法返回 Real) *)
  | B_Arith BAdd, Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Arith BSub, Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Arith BMul, Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Arith BDiv, Tra_Int,  Tra_Int  => Some Tra_Real

  | B_Arith _,    Tra_Int,  Tra_Real => Some Tra_Real
  | B_Arith _,    Tra_Real, Tra_Int  => Some Tra_Real
  | B_Arith _,    Tra_Real, Tra_Real => Some Tra_Real

  | B_Str   BConcat, Tra_String, Tra_String => Some Tra_String

  (* 聚合二元（你写成 binop 了）：max/min Int/Real；mod/divInt Int *)
  | B_Agg BMax,    Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Agg BMin,    Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Agg BMax,    Tra_Real, Tra_Real => Some Tra_Real
  | B_Agg BMin,    Tra_Real, Tra_Real => Some Tra_Real
  | B_Agg BMod,    Tra_Int,  Tra_Int  => Some Tra_Int
  | B_Agg BDivInt, Tra_Int,  Tra_Int  => Some Tra_Int

  | _, _, _ => None
  end.










Fixpoint type_of_rex (in_cols : list Column) (e : rex) : option T_ra :=
  match e with
  | RCol c => 
      match lookup_column in_cols c with
        | Some col => Some (col_ty col)
        | _ => None
      end
  | RLit v => Some (I_ra_type v)
  | RUnop op e1 =>
      match type_of_rex in_cols e1 with
      | Some t1 => unop_type op t1
      | None => None
      end
  | RBinop op e1 e2 =>
      match type_of_rex in_cols e1, type_of_rex in_cols e2 with
      | Some t1, Some t2 => binop_type op t1 t2
      | _, _ => None
      end

  | RSubquery rel c =>
        match lookup_column in_cols c with
        | Some col => Some (col_ty col)
        | _ => None
      end
  end.




Fixpoint cols_of_proj (in_cols : list Column) (ps : list (ColName * rex))
  : option (list Column) :=
  match ps with
  | [] => Some []
  | p :: tl =>
      match type_of_rex in_cols (snd p), cols_of_proj in_cols tl with
      | Some ty, Some rest =>
          Some ({| col_name := fst p; col_ty := ty |} :: rest)
      | _, _ => None
      end
  end.





Fixpoint list_eqb {A : Type}
  (eqb : A -> A -> bool)
  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 =>
      eqb x1 x2 && list_eqb eqb t1 t2
  | _, _ => false
  end.



Definition aggop_out_type (op : aggop) (src_ty : T_ra) : option T_ra :=
  match op, src_ty with
  | AggSize, _ => Some Tra_Int

  | AggMin, Tra_Int  => Some Tra_Int
  | AggMax, Tra_Int  => Some Tra_Int
  | AggSum, Tra_Int  => Some Tra_Int

  | AggMin, Tra_Real => Some Tra_Real
  | AggMax, Tra_Real => Some Tra_Real
  | AggSum, Tra_Real => Some Tra_Real

  | _, _ => None
  end.



Fixpoint cols_of_group (in_cols : list Column) (gcols : list ColName)
  : option (list Column) :=
  match gcols with
  | [] => Some []
  | c :: tl =>
      match lookup_column in_cols c, cols_of_group in_cols tl with
      | Some ty, Some rest =>
          Some ({| col_name := c; col_ty := col_ty ty |} :: rest)
      | _, _ => None
      end
  end.




Fixpoint cols_of_aggs
  (in_cols : list Column)
  (aggs : list (ColName * aggop * ColName))
  : option (list Column) :=
  match aggs with
  | [] => Some []
  | (newc, op, src) :: tl =>
      match lookup_column in_cols src, cols_of_aggs in_cols tl with
      | Some src_ty, Some rest =>
          match aggop_out_type op (col_ty src_ty) with
          | Some out_ty =>
              Some ({| col_name := newc; col_ty := out_ty |} :: rest)
          | None => None
          end
      | _, _ => None
      end
  end.


Fixpoint nodup_stringb (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: tl =>
      negb (existsb (String.eqb x) tl) && nodup_stringb tl
  end.


Definition val_col := "_elem".

Fixpoint cols_of_rel (TS : list TableSchema) (r : rel) : option (list Column) :=
  match r with
  | RAEmpty => Some []

  | RABagLiteral t _vals =>
      Some [mkCol val_col t]

  | RATable tname =>
      match lookup_table_schema TS tname with
      | Some ts => Some (table_cols ts)
      | None => None
      end

  | RASelect _cond r1 =>
      cols_of_rel TS r1

  | RAProject ps r1 =>
      match cols_of_rel TS r1 with
      | Some in_cols => cols_of_proj in_cols ps
      | None => None
      end

  | RACartesian r1 r2
  | RAJoin _ r1 r2 =>
      match cols_of_rel TS r1, cols_of_rel TS r2 with
      | Some c1, Some c2 => Some (List.app c1 c2)  (* 简化版：暂不处理列名冲突 *)
      | _, _ => None
      end

  | RAUnion r1 r2
  | RADiff  r1 r2 =>
      match cols_of_rel TS r1, cols_of_rel TS r2 with
      | Some c1, Some c2 =>
          (* 简化：要求完全相同 *)
          if list_eqb
               (fun a b =>
                  andb (String.eqb a.(col_name) b.(col_name))
                  (* 需要你写 T_ra_eqb *)
                  (T_ra_eqb a.(col_ty) b.(col_ty)))
               c1 c2
          then Some c1 else None
      | _, _ => None
      end

  | RADistinct rel =>
      cols_of_rel TS rel 


  | RAAggregate gcols aggs r1 =>
      (* 这里需要你根据 aggop 规则写输出列；略同我之前给的骨架 *)
      match cols_of_rel TS r1 with
      | None => None
      | Some in_cols =>
          match cols_of_group in_cols gcols, cols_of_aggs in_cols aggs with
          | Some cg, Some ca =>
              let out_cols := List.app cg ca in
              (* 可选：检查输出列名唯一 *)
              if nodup_stringb (map col_name out_cols)
              then Some out_cols
              else None
          | _, _ => None
          end
      end




  end.

