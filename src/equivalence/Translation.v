From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models OCLSyntax RASyntax. 



Definition varEnv := list (var * (ra_rel * list string)).

Fixpoint lookup_var (Gamma : varEnv) (x : var)
  : option (ra_rel * list string) :=
  match Gamma with
  | [] => None
  | (y, U) :: Gamma' =>
      if String.eqb x y
      then Some U
      else lookup_var Gamma' x
  end.



Definition push_var
  (x : var)
  (U : ra_rel * list string)
  (Gamma : varEnv)
  : varEnv :=
  (x, U) :: Gamma.



Definition pop_var (Gamma : varEnv) : varEnv :=
  match Gamma with
  | [] => []
  | _ :: Gamma' => Gamma'
  end.





Fixpoint translate_rex (M : UMLModel) (Gamma : varEnv) (t : tm) : option ra_rex := 
    match t with

    (*  字面量  *)
    (* | CBool b =>
        Some (RVal (V_Bool b)) *)
    | CInt z =>
        Some (RVal (V_Int z))

    | CReal r =>
        Some (RVal (V_Real r))

    | CString s =>
        Some (RVal (V_String s))

    | CObject oid =>
        Some (RVal (V_Object oid))


    (*  一元操作  *)
    | CArithUn op t1 =>
        match translate_rex M Gamma t1 with
        | Some e1 => Some (RArithUn op e1)
        | None => None
        end

    | CStrUn op t1 =>
        match translate_rex M Gamma t1 with
        | Some e1 => Some (RStrUn op e1)
        | None => None
        end




    (*  二元操作  *)
    | CCompBin op t1 t2 =>
        match translate_rex M Gamma t1, translate_rex M Gamma t2 with
        | Some e1, Some e2 =>
            Some (RComp op e1 e2)
        | _, _ => None
        end

    | CArithBin op t1 t2 =>
        match translate_rex M Gamma t1, translate_rex M Gamma t2 with
        | Some e1, Some e2 =>
            Some (RArithBin op e1 e2)
        | _, _ => None
        end

    | CStrBin op t1 t2 =>
        match translate_rex M Gamma t1, translate_rex M Gamma t2 with
        | Some e1, Some e2 =>
            Some (RStrBin op e1 e2)
        | _, _ => None
        end

    | CAggBin op t1 t2 =>
        match translate_rex M Gamma t1, translate_rex M Gamma t2 with
        | Some e1, Some e2 =>
            Some (RAggBin op e1 e2)
        | _, _ => None
        end



    (* String ops with integer arguments *)
    | EAt t1 i =>
        match translate_rex M Gamma t1 with
        | Some e1 => Some (RAt e1 i)
        | None => None
        end

    | ESubstring t1 i j =>
        match translate_rex M Gamma t1 with
        | Some e1 => Some (RSubstring e1 i j)
        | None => None
    end



    | _ =>
        None
    end.








Fixpoint mapM {A B}
  (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs' =>
      match f x, mapM f xs' with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.


Definition eval_literal (t : tm) : option value :=
  match t with
  | CBool b     => Some (V_Bool b)
  | CInt z      => Some (V_Int z)
  | CReal r     => Some (V_Real r)
  | CString s  => Some (V_String s)
  | CObject oid => Some (V_Object oid)
  | _           => None
  end.






Fixpoint lookup_table_schema
  (S : Schema) (t : TableName) : option TableSchema :=
  match S with
  | [] => None
  | ts :: S' =>
      if String.eqb ts.(table_name) t
      then Some ts
      else lookup_table_schema S' t
  end.




Definition row_schema_of_table_schema
  (ts : TableSchema) : RowSchema :=
  map col_name ts.(table_cols).




Fixpoint schema_of (sc : Schema) (q : ra_rel) : list ColName :=
    match q with
    | RAEmpty =>
            [] 

    | RAValues _ =>
        ["elem"]

    | RATable t =>
        match lookup_table_schema sc t with
        | Some ts => row_schema_of_table_schema ts
        | None => []
        end

    | RATableSchema ts =>
        map col_name ts.(table_cols)

    | RASelect _ q1 =>
        schema_of sc q1

    | RAProject ps _ =>
        map proj_name ps

    | RACartesian q1 q2 => 
        schema_of sc q1 ++ schema_of sc q2

    | RAJoin _ q1 q2 =>
        schema_of sc q1 ++ schema_of sc q2

    | RAUnion q1 _ =>
        schema_of sc q1

    | RAIntersect q1 _ =>
        schema_of sc q1

    | RADiff q1 _ =>
        schema_of sc q1

    | RADistinct q1 =>
        schema_of sc q1

    | RAAggregate gcols aggs _ =>
        gcols ++ map (fun '(newc, _, _) => newc) aggs
    end.




(* 取 schema 的最后一列 *)
Definition last_col (cols : list ColName) : option ColName :=
match rev cols with
| [] => None
| c :: _ => Some c
end.


Definition oid_suffix : string := "_id".


Definition ends_with_oid (s : string) : bool :=
  let len_s := String.length s in
  let len_suf := String.length oid_suffix in
  if Nat.ltb len_s len_suf then
    false
  else
    String.eqb
      (String.substring (len_s - len_suf) len_suf s)
      oid_suffix.


Definition remove_oid_suffix (s : string) : string :=
    let len_s := String.length s in
    let len_suf := String.length oid_suffix in
    String.substring 0 (len_s - len_suf) s.


Definition infer_class_from_schema_cols
    (cols : list ColName) : option ClassName :=
    match last_col cols with
    | None => None
    | Some c =>
        if ends_with_oid c then
          Some (remove_oid_suffix c)
        else
          None
    end.

Definition infer_class_from_schema (sc : Schema) (q : ra_rel) : option ClassName :=
    infer_class_from_schema_cols (schema_of sc q).


Definition groupkey := list string.






(* === 小工具：投影 GK / GK_r，以及 GK 等值连接条件 === *)

  
Definition proj_cols (cs : list ColName)
: list RAProjItem :=
map
  (fun c =>
     {| proj_expr := RCol c
      ; proj_name := c |})
  cs.



Fixpoint proj_cols_r (CS : list ColName) : list RAProjItem :=
    match CS with
    | [] => []
    | c :: cs =>
        {| proj_expr := RCol c; proj_name := String.append c "_r" |}
          :: proj_cols_r cs
    end.
  
Fixpoint mk_cols_join_cond (CS : list ColName) : option ra_rex :=
    match CS with
    | [] => None
    | c :: cs =>
        let e0 :=
          RComp BEq (RCol c) (RCol (String.append c "_r")) in
        match mk_cols_join_cond cs with
        | None => Some e0
        | Some e => Some (RBoolBin BAnd e0 e)
        end
    end.
  




























Fixpoint translate_rel (M : UMLModel) (Gamma : varEnv) (t : tm) : option (ra_rel * groupkey) := 
    match t with

    (*  集合（Bag） *)
    | CEmptyBag ty =>
        Some (RAEmpty, [])

    | CBagLiteral ts =>
        match mapM eval_literal ts with
        | Some vs => Some ((RAValues vs), [])
        | None => None
        end


    (*  Var Self  *)
    | CVar x =>
        match lookup_var Gamma x with
        | Some U => Some U
        | None => None
        end

    | CSelf =>
        match lookup_var Gamma "self" with
        | Some U => Some U
        | None => None
        end


    (*  对象 / 属性 / 角色  *)
    | CAttr tm attr  =>

        match translate_rel M Gamma tm with
        | None => None
        | Some (qObj, gks) =>
            (* 假设你能从 qObj 的 schema 中确定 C *)
            match infer_class_from_schema (umlToSchema M) qObj with
            | None => None
            | Some C =>
                let oid := oidColName C in
                let qClass := RATable C in

                let qR :=
                    RAProject
                    [ {| proj_expr := RCol oid;  proj_name := "oid_r" |}
                    ; {| proj_expr := RCol attr; proj_name := attr   |}
                    ]
                    qClass
                    in
                let qJ := 
                    RAJoin
                    (RComp BEq (RCol oid) (RCol "oid_r"))
                    qObj qR
                    in

                Some
                    (RAProject
                        ( map
                            (fun c =>
                               {| proj_expr := RCol c;       proj_name := c   |})
                            (schema_of (umlToSchema M) qObj)
                            ++
                            [{| proj_expr := RCol attr; proj_name := attr |}]
                        )
                        qJ 
                        , gks )

            end
        end


    | CRole tm role =>
        match translate_rel M Gamma tm with
        | None => None
        | Some (qObj, gks) =>
            (* 从对象集合 qObj 的最后一列 oid 推断所属类 C *)
            match infer_class_from_schema (umlToSchema M) qObj with
            | None => None
            | Some C =>
                (* 在 UMLModel 中查找 (C, role) 对应的关联 *)
                match lookup_role_assoc M.(uml_assocs) C role with
                | None => None
                | Some A =>
                    let oidC := oidColName C in
                    let D    := A.(assoc_c2) in
                    let oidD := oidColName D in
    
                    (* 关联表 *)
                    let qAssoc := RATable (assoc_name A) in

                    (* 右侧：关联表，仅保留两端 oid，并将 C 端 oid 重命名为 oid_r *)
                    let qR :=
                      RAProject
                        [ {| proj_expr := RCol oidC; proj_name := "oid_r" |}
                        ; {| proj_expr := RCol oidD; proj_name := oidD    |}
                        ]
                        qAssoc
                    in
    
                    (* 按 C 端 oid 等值连接 *)
                    let qJ :=
                      RAJoin
                        (RComp BEq (RCol oidC) (RCol "oid_r"))
                        qObj qR
                    in
    
                    Some
                    (RAProject
                       (
                         (* 左表原有列全部保留 *)
                         map
                           (fun c =>
                              {| proj_expr := RCol c; proj_name := c |})
                              (schema_of (umlToSchema M) qObj)
                         ++
                         (* 追加右表目标端 oid *)
                         [{| proj_expr := RCol oidD; proj_name := oidD |}]
                       )
                       qJ 
                       , gks )
                end
            end
        end
    

    (* 
        遇到nrole时，将nrole前的rel的所有列作为groupkey记录下来。
        nrole只会发生在obj对象上产生bag，因此后续若进行agg操作，语义是以obj为分组进行agg。
        若在rel->collect(nrole)操作中使用了nrole，此时是对rel集合取nrole的集合
        并进行flatten（见手册11.9.1中对collect操作的语义说明），因此groupkey不变。
    *)
    | CNRole tm nrole =>
        match translate_rel M Gamma tm with
        | None => None
        | Some (qObj, gks) =>
            (* 从对象集合 qObj 的最后一列 oid 推断所属类 C *)
            match infer_class_from_schema (umlToSchema M) qObj with
            | None => None
            | Some C =>
                (* 在 UMLModel 中查找 (C, nrole) 对应的关联 *)
                match lookup_role_assoc M.(uml_assocs) C nrole with
                | None => None
                | Some A =>
                    let oidC := oidColName C in
                    let D    := A.(assoc_c2) in
                    let oidD := oidColName D in

                    (* 关联表 *)
                    let qAssoc := RATable (assoc_name A) in

                    (* 右侧：关联表，仅保留两端 oid，并将 C 端 oid 重命名为 oid_r *)
                    let qR :=
                        RAProject
                        [ {| proj_expr := RCol oidC; proj_name := "oid_r" |}
                        ; {| proj_expr := RCol oidD; proj_name := oidD    |}
                        ]
                        qAssoc
                    in

                    (* 按 C 端 oid 等值连接（1:n 展开点） *)
                    let qJ :=
                        RAJoin
                        (RComp BEq (RCol oidC) (RCol "oid_r"))
                        qObj qR
                    in

                    let qOut :=
                        RAProject
                        (
                            (* 左表原有列全部保留 *)
                            map
                            (fun c =>
                                {| proj_expr := RCol c; proj_name := c |})
                            (schema_of (umlToSchema M) qObj)
                            ++
                            (* 追加右表目标端 oid（nrole 的结果） *)
                            [{| proj_expr := RCol oidD; proj_name := oidD |}]
                        )
                        qJ
                    in

                    Some (qOut, schema_of (umlToSchema M) qObj)
                end
            end
        end



    (*  allInstances  *)
    (* 转换规则为，从class表中投影出oid列，groupkey为空 *)
    | CAllInstances class =>
        let oid := oidColName class in
        let qClass := RATable class in
        Some
        ( RAProject
            [ {| proj_expr := RCol oid; proj_name := oid |} ]
            qClass
        , [] (* groupkey 为空 *)
        )


      
    (*  一元布尔操作  *)
    (* 操作逻辑为，找出varEnv顶端的var对应的全集，用全集和当前tm对应的ra_rel进行差集操作，groupkey为空 *)
    | CBoolUn op tm =>
        match op with
        | UNot =>
            (* 先翻译子表达式 *)
            match translate_rel M Gamma tm with
            | None => None
            | Some (qTrue, _) =>
                (* 取当前上下文的全集（varEnv 栈顶） *)
                match Gamma with
                | [] => None
                | (_, (qAll, _)) :: _ =>
                    (* 差集：全集 - 满足 tm 的集合 *)
                    Some
                    ( RADiff qAll qTrue
                    , []   (* 布尔结果不携带 groupkey *)
                    )
                end
            end
        end



    (*  二元布尔操作  *)
    | CBoolBin op t1 t2 =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (q1, _), Some (q2, _) =>
            match op with
            | BAnd =>
                (* a and b  ≡  a ∩ b *)
                Some ( RAIntersect q1 q2
                    , [] )

            | BOr  =>
                (* a or b   ≡  a ∪ b *)
                Some ( RAUnion q1 q2
                    , [] )

            | BXor =>
                (* a xor b = (a − b) ∪ (b − a) *)
                let qAminusB := RADiff q1 q2 in
                let qBminusA := RADiff q2 q1 in
                Some ( RAUnion qAminusB qBminusA
                        , [] )

            | BImplies =>
                (* a implies b  ≡  (not a) or b *)
                (*             ≡  (All − a) ∪ b *)
                match Gamma with
                | [] => None
                | (_, (qAll, _)) :: _ =>
                    let qNotA := RADiff qAll q1 in
                    Some ( RAUnion qNotA q2
                        , [] )
                end
            end
        | _, _ => None
        end




    (*  Bag 运算  *)
    (*  Bag union  *)
    | CUnion t1 t2 =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (q1, gk1), Some (q2, gk2) =>

            match gk1, gk2 with
            | [], [] =>
                (* 情况 1：[] × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RAUnion
                            (RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1)
                            (RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2)
                        , [] )
                | _, _ =>
                    None
                end

            | [], GK =>
            (* 情况 2：[] × GK *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q2 in
                    let qS  := RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v2])) q2 in
                    Some ( RAUnion qLift qG
                        , GK )
                | _, _ =>
                    None
                end
            | GK, [] =>
            (* 情况 3：GK × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q1 in
                    let qS  := RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v1])) q1 in
                    Some ( RAUnion qG qLift
                        , GK )
                | _, _ =>
                    None
                end
            | GK, _ =>
            (* 情况 4：GK1 × GK2 *)
                (* 假设 gk1 = gk2 *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RAUnion
                            (RAProject (proj_cols (GK ++ [v1])) q1)
                            (RAProject (proj_cols (GK ++ [v2])) q2)
                        , GK )
                | _, _ =>
                    None
                end
            end
        | _, _ => None
        end


    (*  Bag intersect  *)
    | CIntersect t1 t2  =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (q1, gk1), Some (q2, gk2) =>

            match gk1, gk2 with
            | [], [] =>
                (* 情况 1：[] × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RAIntersect
                            (RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1)
                            (RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2)
                        , [] )
                | _, _ =>
                    None
                end

            | [], GK =>
            (* 情况 2：[] × GK *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q2 in
                    let qS  := RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v2])) q2 in
                    Some ( RAIntersect qLift qG
                        , GK )
                | _, _ =>
                    None
                end
            | GK, [] =>
            (* 情况 3：GK × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q1 in
                    let qS  := RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v1])) q1 in
                    Some ( RAIntersect qG qLift
                        , GK )
                | _, _ =>
                    None
                end
            | GK, _ =>
            (* 情况 4：GK1 × GK2 *)
                (* 假设 gk1 = gk2 *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RAIntersect
                            (RAProject (proj_cols (GK ++ [v1])) q1)
                            (RAProject (proj_cols (GK ++ [v2])) q2)
                        , GK )
                | _, _ =>
                    None
                end
            end
        | _, _ => None
        end



    (*  Bag difference  *)
    | CDifference t1 t2  =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (q1, gk1), Some (q2, gk2) =>

            match gk1, gk2 with
            | [], [] =>
                (* 情况 1：[] × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RADiff
                            (RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1)
                            (RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2)
                        , [] )
                | _, _ =>
                    None
                end

            | [], GK =>
            (* 情况 2：[] × GK *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q2 in
                    let qS  := RAProject [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v2])) q2 in
                    Some ( RADiff qLift qG
                        , GK )
                | _, _ =>
                    None
                end
            | GK, [] =>
            (* 情况 3：GK × [] *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK := RAProject (proj_cols GK) q1 in
                    let qS  := RAProject [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2 in
                    let qLift := RACartesian qGK qS in
                    let qG := RAProject (proj_cols (GK ++ [v1])) q1 in
                    Some ( RADiff qG qLift
                        , GK )
                | _, _ =>
                    None
                end
            | GK, _ =>
            (* 情况 4：GK1 × GK2 *)
                (* 假设 gk1 = gk2 *)
                match last_col (schema_of (umlToSchema M) q1),
                last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    Some
                        ( RADiff
                            (RAProject (proj_cols (GK ++ [v1])) q1)
                            (RAProject (proj_cols (GK ++ [v2])) q2)
                        , GK )
                | _, _ =>
                    None
                end
            end
        | _, _ => None
        end



    | CSymDiff t1 t2 =>
        match translate_rel M Gamma t1,
              translate_rel M Gamma t2 with
        | Some (q1, gk1), Some (q2, gk2) =>
    
            match gk1, gk2 with
            | [], [] =>
                (* 单集合 xor *)
                match last_col (schema_of (umlToSchema M) q1),
                      last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let q12 :=
                      RADiff
                        (RAProject
                           [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1)
                        (RAProject
                           [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2)
                    in
                    let q21 :=
                      RADiff
                        (RAProject
                           [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2)
                        (RAProject
                           [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1)
                    in
                    Some (RAUnion q12 q21, [])
                | _, _ => None
                end
    
            | [], GK =>
                (* [] × GK *)
                match last_col (schema_of (umlToSchema M) q1),
                      last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK   := RAProject (proj_cols GK) q2 in
                    let qS    := RAProject
                                   [ {| proj_expr := RCol v1; proj_name := v1 |} ] q1 in
                    let qLift := RACartesian qGK qS in
                    let qG    := RAProject (proj_cols (GK ++ [v2])) q2 in
    
                    let q12 := RADiff qLift qG in
                    let q21 := RADiff qG qLift in
                    Some (RAUnion q12 q21, GK)
                | _, _ => None
                end
    
            | GK, [] =>
                (* GK × []，对称 *)
                match last_col (schema_of (umlToSchema M) q1),
                      last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let qGK   := RAProject (proj_cols GK) q1 in
                    let qS    := RAProject
                                   [ {| proj_expr := RCol v2; proj_name := v2 |} ] q2 in
                    let qLift := RACartesian qGK qS in
                    let qG    := RAProject (proj_cols (GK ++ [v1])) q1 in
    
                    let q12 := RADiff qG qLift in
                    let q21 := RADiff qLift qG in
                    Some (RAUnion q12 q21, GK)
                | _, _ => None
                end
    
            | GK, _ =>
                (* GK × GK *)
                match last_col (schema_of (umlToSchema M) q1),
                      last_col (schema_of (umlToSchema M) q2) with
                | Some v1, Some v2 =>
                    let q1' := RAProject (proj_cols (GK ++ [v1])) q1 in
                    let q2' := RAProject (proj_cols (GK ++ [v2])) q2 in
                    let q12 := RADiff q1' q2' in
                    let q21 := RADiff q2' q1' in
                    Some (RAUnion q12 q21, GK)
                | _, _ => None
                end
            end
        | _, _ => None
        end
    




    (*  Bag 谓词  *)

    | CIncludesAll t1 t2 =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (qA, gkA), Some (qB, gkB) =>


            (* 取两个 bag 的元素列 *)
            match last_col (schema_of (umlToSchema M) qA),
                last_col (schema_of (umlToSchema M) qB) with
            | Some vA, Some vB =>

                match gkA, gkB with
                | [], [] =>
                    (* 统一投影为 elem *)
                    let qA' :=
                    RAProject
                        [ {| proj_expr := RCol vA; proj_name := "elem" |} ]
                        qA
                    in

                    let qB' :=
                    RAProject
                        [ {| proj_expr := RCol vB; proj_name := "elem" |} ]
                        qB
                    in

                    (* A ∩ B *)
                    let qInter :=
                    RAIntersect qA' qB'
                    in

                    (* |B| *)
                    let qCntB :=
                    RAAggregate
                        []
                        [ ("b_count", AggSize, "elem") ]
                        qB'
                    in

                    (* |A ∩ B| *)
                    let qCntI :=
                    RAAggregate
                        []
                        [ ("i_count", AggSize, "elem") ]
                        qInter
                    in

                    (* 将两个 count 放到同一行 *)
                    let qCnt :=
                    RACartesian qCntB qCntI
                    in

                    (* 条件：b_count = i_count *)
                    let qCond :=
                    RASelect
                        (RComp BEq (RCol "b_count") (RCol "i_count"))
                        qCnt
                    in

                    (* EXISTS(qCond) *)
                    let qExists :=
                    RAProject [] qCond
                    in

                    (* 取当前上下文对象集合 *)
                    match Gamma with
                    | (_, (qCtx, _)) :: _ =>

                        (* scalarQuery 模式：
                        if EXISTS(qCond) then qCtx else ∅ *)
                        let qRes :=
                        RADiff
                            qCtx
                            (RADiff qCtx qExists)
                        in
                        Some (qRes, [])
                    | _ => None
                    end


                | [], GK =>
                    (* set2 分组：GK + elem *)
                    let qB' :=
                      RAProject
                        (proj_cols GK ++ [{| proj_expr := RCol vB; proj_name := "elem_r" |}])
                        qB
                    in
                
                    (* set2GroupAndCount：按 GK 计 b_count *)
                    let qBGroupCnt :=
                      RAAggregate GK [("b_count", AggSize, "elem_r")] qB'
                    in
                
                    (* set1：单集合 elem *)
                    let qAelem :=
                      RAProject [ {| proj_expr := RCol vA; proj_name := "elem" |} ] qA
                    in
                
                    (* innerJoin：按 elem 等值连接（相当于取交集） *)
                    let qJoin :=
                      RAJoin (RComp BEq (RCol "elem") (RCol "elem_r")) qAelem qB'
                    in
                
                    (* innerJoin 聚合：按 GK 计 i_count *)
                    let qInnerCnt :=
                      RAAggregate GK [("i_count", AggSize, "elem_r")] qJoin
                    in
                
                    let qRes :=
                      RAJoin (RComp BEq (RCol "b_count") (RCol "i_count")) qBGroupCnt qInnerCnt
                    in


                    (* 为避免 GK 列名冲突，右侧 GK 重命名为 *_r *)
                    let qInnerCnt_r :=
                    RAProject
                        (proj_cols_r GK ++ [{| proj_expr := RCol "i_count"; proj_name := "i_count" |}])
                        qInnerCnt
                    in

                    (* join 条件：GK = GK_r ∧ b_count = i_count *)
                    match mk_cols_join_cond GK with
                    | None => None
                    | Some gkCond =>
                        let qCond :=
                        RBoolBin BAnd
                            gkCond
                            (RComp BEq (RCol "b_count") (RCol "i_count"))
                        in

                        (* 满足 includesAll 的分组 *)
                        let qRes :=
                        RAProject
                            (proj_cols GK)
                            (RAJoin qCond qBGroupCnt qInnerCnt_r)
                        in

                        Some (qRes, GK)
                    end


                | GK, [] =>
                    (* 分组集合：GK + elem *)
                    let qA' :=
                      RAProject
                        (proj_cols GK ++ [{| proj_expr := RCol vA; proj_name := "elem" |}])
                        qA
                    in
                
                    (* 单个集合：elem_r *)
                    let qB' :=
                      RAProject
                        [{| proj_expr := RCol vB; proj_name := "elem_r" |}]
                        qB
                    in
                
                    (* innerJoin：按元素等值连接，得到交集 *)
                    let qJoin :=
                      RAJoin
                        (RComp BEq (RCol "elem") (RCol "elem_r"))
                        qA' qB'
                    in
                
                    (* 对交集按 GK 聚合，统计 i_count *)
                    let qInnerCnt :=
                      RAAggregate
                        GK
                        [("i_count", AggSize, "elem")]
                        qJoin
                    in
                
                    (* 计算单个集合基数 |B|，无 groupkey，是一行关系 *)
                    let qBCnt :=
                      RAAggregate
                        []
                        [("b_count", AggSize, "elem_r")]
                        qB'
                    in
                
                
                    (* join 条件：i_count = b_count *)
                    let qCond :=
                      RComp BEq (RCol "i_count") (RCol "b_count")
                    in
                
                    (* 满足 includesAll 的分组 *)
                    let qRes :=
                      RAProject
                        (proj_cols GK)
                        (RAJoin qCond qInnerCnt qBCnt)
                    in
                
                    Some (qRes, GK)
                


                | GK, _ =>
                    (* 假设 GK1 = GK2 = GK *)
                
                    (* 左侧分组集合：GK + elem *)
                    let qA' :=
                      RAProject
                        (proj_cols GK ++ [{| proj_expr := RCol vA; proj_name := "elem" |}])
                        qA
                    in
                
                    (* 右侧分组集合：GK + elem_r *)
                    let qB' :=
                      RAProject
                        (proj_cols GK ++ [{| proj_expr := RCol vB; proj_name := "elem_r" |}])
                        qB
                    in
                
                    (* set2GroupAndCount：按 GK 计 b_count *)
                    let qBGroupCnt :=
                      RAAggregate GK [("b_count", AggSize, "elem_r")] qB'
                    in
                
                    (* innerJoin：GK 等值 ∧ elem 等值（分组内交集） *)
                    match mk_cols_join_cond GK with
                    | None => None
                    | Some gkCond =>
                        let qJoinCond :=
                          RBoolBin BAnd
                            gkCond
                            (RComp BEq (RCol "elem") (RCol "elem_r"))
                        in
                
                        let qJoin :=
                          RAJoin qJoinCond qA' qB'
                        in
                
                        (* 对交集按 GK 聚合，计 i_count *)
                        let qInnerCnt :=
                          RAAggregate GK [("i_count", AggSize, "elem")] qJoin
                        in
                
                        (* 为避免 GK 列名冲突，将 qInnerCnt 的 GK 重命名为 *_r *)
                        let qInnerCnt_r :=
                          RAProject
                            (proj_cols_r GK ++ [{| proj_expr := RCol "i_count"; proj_name := "i_count" |}])
                            qInnerCnt
                        in
                
                        (* join 条件：GK = GK_r ∧ i_count = b_count *)
                        let qCond :=
                          RBoolBin BAnd
                            gkCond
                            (RComp BEq (RCol "i_count") (RCol "b_count"))
                        in
                
                        (* 满足 includesAll 的分组 *)
                        let qRes :=
                          RAProject
                            (proj_cols GK)
                            (RAJoin qCond qBGroupCnt qInnerCnt_r)
                        in
                
                        Some (qRes, GK)
                    end
                
                end

            | _, _ => None
            end


        | _, _ => None
        end


    (*  Bag 谓词  *)
    | CExcludesAll t1 t2 =>
        match translate_rel M Gamma t1,
            translate_rel M Gamma t2 with
        | Some (qA, gkA), Some (qB, gkB) =>

            match gkA, gkB with

            (*************************************************************)
            (* 1. 单个集合 × 单个集合                                   *)
            (*    A excludesAll B  ⇔  A ∩ B = ∅                          *)
            (*************************************************************)
            | [], [] =>
                match last_col (schema_of (umlToSchema M) qA),
                    last_col (schema_of (umlToSchema M) qB) with
                | Some vA, Some vB =>

                    let qA' :=
                    RAProject
                        [{| proj_expr := RCol vA; proj_name := "elem" |}]
                        qA
                    in
                    let qB' :=
                    RAProject
                        [{| proj_expr := RCol vB; proj_name := "elem_r" |}]
                        qB
                    in

                    (* A ∩ B *)
                    let qInter :=
                    RAJoin
                        (RComp BEq (RCol "elem") (RCol "elem_r"))
                        qA' qB'
                    in

                    (* |A ∩ B| *)
                    let qCnt :=
                    RAAggregate [] [("i_count", AggSize, "elem")] qInter
                    in

                    (* i_count = 0 *)
                    let qCond :=
                    RASelect
                        (RComp BEq (RCol "i_count") (RVal (V_Int 0)))
                        qCnt
                    in

                    (* EXISTS(qCond) *)
                    let qExists := RAProject [] qCond in

                    (* if true return context, else empty *)
                    match Gamma with
                    | (_, (qCtx, _)) :: _ =>
                        Some
                        ( RADiff qCtx (RADiff qCtx qExists)
                        , [] )
                    | _ => None
                    end
                | _, _ => None
                end

            (*************************************************************)
            (* 2. 单个集合 × 分组集合                                   *)
            (*    返回不与 A 有交集的分组                                *)
            (*************************************************************)
            | [], GK =>
                match last_col (schema_of (umlToSchema M) qA),
                    last_col (schema_of (umlToSchema M) qB) with
                | Some vA, Some vB =>

                    let qA' :=
                    RAProject
                        [{| proj_expr := RCol vA; proj_name := "elem" |}]
                        qA
                    in

                    let qB' :=
                    RAProject
                        (proj_cols GK ++
                        [{| proj_expr := RCol vB; proj_name := "elem_r" |}])
                        qB
                    in

                    let qJoin :=
                    RAJoin
                        (RComp BEq (RCol "elem") (RCol "elem_r"))
                        qA' qB'
                    in

                    let qCnt :=
                    RAAggregate GK [("cnt", AggSize, "elem_r")] qJoin
                    in

                    let qRes :=
                    RASelect
                        (RComp BEq (RCol "cnt") (RVal (V_Int 0)))
                        qCnt
                    in

                    Some (RAProject (proj_cols GK) qRes, GK)

                | _, _ => None
                end

            (*************************************************************)
            (* 3. 分组集合 × 单个集合                                   *)
            (*    返回与 B 无交集的分组                                  *)
            (*************************************************************)
            | GK, [] =>
                match last_col (schema_of (umlToSchema M) qA),
                    last_col (schema_of (umlToSchema M) qB) with
                | Some vA, Some vB =>

                    let qA' :=
                    RAProject
                        (proj_cols GK ++
                        [{| proj_expr := RCol vA; proj_name := "elem" |}])
                        qA
                    in

                    let qB' :=
                    RAProject
                        [{| proj_expr := RCol vB; proj_name := "elem_r" |}]
                        qB
                    in

                    let qJoin :=
                    RAJoin
                        (RComp BEq (RCol "elem") (RCol "elem_r"))
                        qA' qB'
                    in

                    let qCnt :=
                    RAAggregate GK [("cnt", AggSize, "elem")] qJoin
                    in

                    let qRes :=
                    RASelect
                        (RComp BEq (RCol "cnt") (RVal (V_Int 0)))
                        qCnt
                    in

                    Some (RAProject (proj_cols GK) qRes, GK)

                | _, _ => None
                end

            (*************************************************************)
            (* 4. 分组集合 × 分组集合                                   *)
            (*    分组内 excludesAll                                    *)
            (*************************************************************)
            | GK1, GK2 =>
                (* 假设 GK1 = GK2 *)
                let GK := GK1 in
                match last_col (schema_of (umlToSchema M) qA),
                    last_col (schema_of (umlToSchema M) qB),
                    mk_cols_join_cond GK with
                | Some vA, Some vB, Some gkCond =>

                    let qA' :=
                    RAProject
                        (proj_cols GK ++
                        [{| proj_expr := RCol vA; proj_name := "elem" |}])
                        qA
                    in

                    let qB' :=
                    RAProject
                        (proj_cols GK ++
                        [{| proj_expr := RCol vB; proj_name := "elem_r" |}])
                        qB
                    in

                    let qJoinCond :=
                    RBoolBin BAnd
                        gkCond
                        (RComp BEq (RCol "elem") (RCol "elem_r"))
                    in

                    let qJoin :=
                    RAJoin qJoinCond qA' qB'
                    in

                    let qCnt :=
                    RAAggregate GK [("cnt", AggSize, "elem")] qJoin
                    in

                    let qRes :=
                    RASelect
                        (RComp BEq (RCol "cnt") (RVal (V_Int 0)))
                        qCnt
                    in

                    Some (RAProject (proj_cols GK) qRes, GK)

                | _, _, _ => None
                end
            end

        | _, _ => None
        end





(*  
    | CIncludes t1 t2 =>
        None

    | CExcludes t1 t2 =>
        None

    | CIsEmpty tm =>
        None

    | CNotEmpty tm =>
        None
        
    | CIsUnique tm =>
        None


    (*  Iterator *)

    | CForAll  =>
        None

    | CExists  =>
        None

    | CSelect  =>
        None

    | CReject  =>
        None

    | COne  =>
        None

    | CCollect  =>
        None

    | CRCollect  =>
        None

    | CNRCollect  =>
        None


    (*  bag聚合  *)
    | EAggregate : aggop -> tm -> tm 

 *)


    | _ =>
        None
    end.