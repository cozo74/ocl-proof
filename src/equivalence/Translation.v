From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models OCLSyntax RASyntax RASemantic OCLTyping Utils. 











(* 取 schema 的最后一列 *)
Definition last_col (cols : list ColName) : option ColName :=
    match rev cols with
    | [] => None
    | c :: _ => Some c
    end.




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
  


Fixpoint mk_cols_join_cond (CS : list ColName) : option rex :=
    match CS with
    | [] => None
    | c :: cs =>
        let e0 :=
          RBinop (B_Comp BEq)  (RCol c) (RCol (String.append c "_r")) in
        match mk_cols_join_cond cs with
        | None => Some e0
        | Some e => Some (RBinop (B_Bool BAnd) e0 e)
        end
    end.
  





Definition last_col_ty (cols : list Column) : option T_ra :=
  match rev cols with
  | [] => None
  | c :: _ => Some (col_ty c)
  end.


(* 求两个list var_name的交集（去重）, keep_left *)
Definition inter_var (l1 l2 : list var_name) : list var_name :=
  filter (fun x => existsb (String.eqb x) l2) l1.


(* 求两个list var_name的并集（去重）, keep_left *)
Fixpoint union_var (l1 l2 : list var_name) : list var_name :=
  match l2 with
  | [] => l1
  | x :: xs =>
      if existsb (String.eqb x) l1
      then union_var l1 xs
      else union_var (List.app l1 [x]) xs
  end.





Inductive rex_or_rel : Type :=
    | Rex : rex -> rex_or_rel
    | Rel : rel -> rex_or_rel.


Definition tran_env := partial_map (rel * list var_name * T_h).


Definition val_col := "_elem".
Definition val_col_r := "_elem_r".


Fixpoint translate (M : object_model) (E : tran_env) (t : tm) : option (rex_or_rel * list var_name * T_e) := 
    match t with

    
    (* ======================== Var 表达式 ======================== *)
    (* 
        转换规则:
        - 从tran_env中查找变量x的替换rel
        - 将x加入rel的依赖变量中，表示当前表达式的取值依赖变量x
        - 表达式的类型为原rel的类型
    *)
    | CVar x =>
        match E x with
        | Some (r, vl, th) => Some (Rel r, List.app vl [x], Te_Single th)
        | None => None
        end




    (* ======================== operation 表达式 ======================== *)

    (*  无参operation： 字面量构造器  *)
    (* 
        转换规则:
        - 根据basic type字面量的值，创建对应的Rex，表示一个标量
        - 一个标量不存在依赖变量，依赖变量列表为空
        - 类型为值的类型
    *)
    | CLit v => 
        match v with
          |  Ib_Bool b => Some (Rex (RLit (Ira_Bool b)), [], Te_Single (Th_Basic Tb_Bool))
          |  Ib_Int z => Some (Rex (RLit (Ira_Int z)), [], Te_Single (Th_Basic Tb_Int))
          |  Ib_Real r => Some (Rex (RLit (Ira_Real r)), [], Te_Single (Th_Basic Tb_Real))
          |  Ib_String s => Some (Rex (RLit (Ira_String s)), [], Te_Single (Th_Basic Tb_String))
        end




    (*  basic type 有参operation： 一元操作  *)
    (* 
        转换规则:
        - 若t为rex
            - 转换为Rex的一元操作
            - 一个标量不存在依赖变量，依赖变量列表为空
            - 类型由OCLTyping中unop_type函数计算得到
        - 若t为rel
            - 转换为Rel上的Project操作
                - 保留所有列
                - 将val_col列根据unop变换为新列
            - 依赖变量列表与源rel一致
            - 类型由OCLTyping中unop_type函数计算得到
    *)
    | CUnop op t =>
        match translate M E t with
        (* rex *)
        | Some (Rex e1, [], te) =>
            match unop_type op te with 
            | Some te' => 
                Some (Rex (RUnop op e1), [], te')
            | _ => None
            end
        (* rel *)
        | Some (Rel q, vl, te) =>
            match unop_type op te with 
            | Some te' => 
                let vcols := proj_cols vl in
                let nv := mkProj val_col (RUnop op (RCol val_col)) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) q),
                    vl,
                    te'
                )
            | _ => None
            end
        | _ => None
        end



    (*  basic type 有参operation： 二元操作 (和object type eq)  *)
    (* 
        转换规则:
        - 若t1为rex，t2为rex
            - 转换为Rex的二元操作
            - 一个标量不存在依赖变量，依赖变量列表为空
            - 类型由OCLTyping中binop_type函数计算得到
        - 若t1为rex，t2为rel
        - 若t1为rel，t2为rex
            - 转换为Rel上的Project操作
                - 保留所有列
                - 将val_col列根据binop变换为新列
            - 依赖变量列表与源rel一致
            - 类型由OCLTyping中binop_type函数计算得到
        - 若t1为rel，t2为rel
            - 准换为两个rel的join+project操作
                - join条件为：所有相同依赖变量相等
                - 对join结果进行投影，投影出两个依赖变量列表的并集（去重），
                    将val_col列根据binop变换为新列
            - 依赖变量列表为两个依赖变量列表的并集（去重）
            - 类型由OCLTyping中binop_type函数计算得到
    *)

    | CBinop op t1 t2 =>
        match translate M E t1, translate M E t2 with
        (* rex 与 rex *)
        | Some (Rex e1, [], te1), Some (Rex e2, [], te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                Some (Rex (RBinop op e1 e2), [], te')
            | _ => None
            end
        (* rex 与 rel *)
        | Some (Rex e1, [], te1), Some (Rel q2, vl2, te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                let vcols := proj_cols vl2 in
                let nv := mkProj val_col (RBinop op e1 (RCol val_col)) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) q2),
                    vl2,
                    te'
                )
            | _ => None
            end

        (* rel 与 rex *)
        | Some (Rel q1, vl1, te1), Some (Rex e2, [], te2) =>
            match binop_type op te1 te2 with 
            | Some te' =>
                let vcols := proj_cols vl1 in
                let nv := mkProj val_col (RBinop op (RCol val_col) e2) in
                Some (
                    Rel (RAProject (List.app vcols [nv]) q1),
                    vl1,
                    te'
                )
            | _ => None
            end

        (* rel 与 rel *)
        (* join时将右表相同列重命名为带_r后缀 *)
        | Some (Rel q1, vl1, te1), Some (Rel q2, vl2, te2) =>
            let intercols := inter_var vl1 vl2 in
            let unioncols := union_var vl1 vl2 in 
            match binop_type op te1 te2 with 
            | Some te' =>
                let cond := mk_cols_join_cond intercols in
                let procols := (proj_cols unioncols) [] in
                let nv := mkProj val_col (RBinop op (RCol val_col) (RCol val_col_r)) in
                RAProject procols (RAJoin cond q1 q2)


            | _ => None
            end
        | _, _ => None
        end




    (*  object type 有参operation： allInstances, 对象属性/角色  *)
    (* | CAllInstances class =>
        match lookup_table (sc_data M) class with
        | Some table =>
            Some ( Rel ( RAProject [(mkProj val_col (RCol oid_col))] (RATable class)))
        | None => None
        end *)



    (* | CAttr tm attr =>
        match translate M E tm with
        (* 
            1. tm 成功转换为一个表示cn类型对象的 rel
            2. 从 schema中成功查找到该类对应的表存在attr字段，表示对象表objTable存在、字段存在
            3. 将tm转换的结果rel和 对象对应的表objTable进行连接操作，
                连接条件为rel的最后一列（val_col）和对象表objTable的oid_col相等，
            4. 最后投影出rel中除了val_col的所有列，以及将objTable中的attr列投影为val_col列，
                类型为attr的类型
        *)




        | Some (Rel q) =>
            match cols_of_rel (sc_data SC) q with
            | Some cols =>
                match last_col_ty cols with 
                | Some (Tra_Object cn) =>
                    match lookup_table_column SC cn attr with
                    Some acol =>
                        let cond :=  RBinop (B_Comp BEq) (RCol val_col) (RCol attr) in
                        let join_res := RAJoin cond q (RATable cn) in 
                        let vd_cols := proj_cols (removelast (map col_name cols)) in
                        Some 
                        (
                            Rel 
                            (RAProject 
                            (List.app vd_cols [mkProj val_col (RCol attr) ] )
                            join_res)
                        )
                    | _ => None
                    end
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end  *)


    | CRole tm role =>
        None  (* 见下面注释 *)


    | CNRole tm nrole =>
        None  (* 见下面注释 *)



    (* | CBagLiteral ts =>
        match mapM eval_literal ts with
        | Some vs => Some ((RAValues vs), [])
        | None => None
        end *)










    (*  对象 / 属性 / 角色  *)
    (* | CAttr tm attr  =>

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
        end *)


    (* | CRole tm role =>
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
        end *)
    

    (* 
        遇到nrole时，将nrole前的rel的所有列作为groupkey记录下来。
        nrole只会发生在obj对象上产生bag，因此后续若进行agg操作，语义是以obj为分组进行agg。
        若在rel->collect(nrole)操作中使用了nrole，此时是对rel集合取nrole的集合
        并进行flatten（见手册11.9.1中对collect操作的语义说明），因此groupkey不变。
    *)

    (* 
        Invariant（groupkey 不变量）
        对任意 (q, GK)：

        GK = [] 表示 q 描述的是一个全局 Bag

        GK ≠ [] 表示 q 描述的是一个 按 GK 分组的 Bag family

        所有 RA 运算都必须保持这一解释一致
    *)


    (* | CNRole tm nrole =>
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
        end *)



    (*  allInstances  *)
    (* 转换规则为，从class表中投影出oid列，groupkey为空 *)
    (* | CAllInstances class =>
        let oid := oidColName class in
        let qClass := RATable class in
        Some
        ( RAProject
            [ {| proj_expr := RCol oid; proj_name := oid |} ]
            qClass
        , [] (* groupkey 为空 *)
        ) *)


      
    (*  一元布尔操作  *)
    (* 操作逻辑为，找出varEnv顶端的var对应的全集，用全集和当前tm对应的ra_rel进行差集操作，groupkey为空 *)
    (* | CBoolUn op tm =>
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
        end *)



    (*  二元布尔操作  *)
    (* | CBoolBin op t1 t2 =>
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
        end *)




    (*  Bag 运算  *)
    (*  Bag union  *)
    (* | CUnion t1 t2 =>
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
        end *)




    (*  Bag difference  *)
    (* | CDifference t1 t2  =>
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
        end *)








        
    (* | CSelect t1 var t2 =>
        match translate_rel M Gamma t1 with
        | Some (qSet, GK) =>
    
            (* push scope: var ↦ qSet *)
            let Gamma' := push_var var (qSet, GK) Gamma in
    
            match translate_rel M Gamma' t2 with
            | Some (qBool, GK') =>
    
                (* 语义约束（设计不变式）：
                   - qBool 与 qSet schema 相同
                   - GK' = GK
                   在翻译阶段不显式检查，作为不变式假设 *)
    
                Some (qBool, GK)
    
            | _ => None
            end
    
        | _ => None
        end *)
    








    (*  bag 聚合  *)

    (* 
        设计约束：
        对单集合的聚合（size / min / max / sum / avg）不产生数值表达式，而产生一行关系；
        该结果只能用于布尔判断（如 =、>、<），不能参与算术运算。
    *)
    (* | EAggregate op t =>
        match translate_rel M Gamma t with
        | Some (qSet, GK) =>

            (* 取最后一列作为聚合列 *)
            match last_col (schema_of (umlToSchema M) qSet) with
            | None => None
            | Some v =>

                (* =============================== *)
                (* 统一：关系级聚合（不产生标量） *)
                (* =============================== *)
                let qAgg :=
                RAAggregate
                    GK
                    [(agg_col_name op v, op, v)]
                    qSet
                in

                Some (qAgg, GK)
            end

        | _ => None
        end *)




    | _ =>
        None
    end.