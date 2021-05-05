From Cofq.SystemK Require Import
     SystemKDefinitions.
From Cofq.SystemF Require Import
     SystemFDefinitions
     SystemFTyping.

Require Import List.
Import ListNotations.

Definition cps_translate_type_cont (t : KType) : KType :=
    KTForall 0 [t]
.
Fixpoint cps_translate_type {I} `{FInt I} (t : FType) : KType :=
    match t with
    | Arrow t_in t_out =>
        KTForall 0 [
            cps_translate_type t_in;
            cps_translate_type_cont (cps_translate_type t_out)
        ] 
    | Prod ts =>
        KProd (map (fun t' => cps_translate_type t') ts)
    | TForall body =>
        KTForall 1 [cps_translate_type_cont (cps_translate_type body)]
    | TVar index =>
        KTVar index
    (* Base Types *)
    | IntType =>
        KIntType
    end
.

Definition nat_as_var_ind (n : nat) : VarInd. Admitted.

(* TODO infer types on the System F side, annotated on the System K side *)
(* FIXME check everything for variable lifting *)
Fixpoint cps_translate_term {I} `{FInt I} (t : Term) (k : KValue): KTerm :=
    let ktypeof (fvalue : Term) : KType :=
        let ftype := match (typeof fvalue) with
        | Some type => type
        | None => IntType (* FIXME: this is a poor excuse for an exception *)
        end in
        cps_translate_type ftype
    in
    let continue (fvalue : Term) (kvalue : KRawValue) : KTerm :=
        KApp k [] [KAnnotated (ktypeof fvalue) kvalue]
    in
    match t with
    | Var index =>
        continue t (KVar index)
    | Ann term type =>
        cps_translate_term term k
    | Fix arg_type ret_type body =>
        let arg_ktype := cps_translate_type arg_type in
        let ret_ktype := cps_translate_type ret_type in
        let ret_ktypecont := cps_translate_type_cont ret_ktype in
        let kfix_arg_types := [arg_ktype; ret_ktypecont] in
        let kvalue_thunk := KFix 0 kfix_arg_types (cps_translate_term body (KAnnotated (cps_translate_type ret_type) (KVar 0))) in
        continue t kvalue_thunk
    | Num num =>
        continue t (KNum num)
    | App f x =>
        (* TODO VARIABLE LIFTING *)
        let k_f_type := ktypeof f in
        let k_x_type := ktypeof x in
        let k_f_var := KAnnotated k_f_type (KVar 1) in
        let k_x_var := KAnnotated k_x_type (KVar 0) in
        let x_cont_body := KApp k_f_var [] [k_x_var; k] in
        let x_cont := KFix 0 [k_x_type] x_cont_body in
        let x_cont_ann := KAnnotated (KTForall 0 [k_x_type]) x_cont in
        let f_cont_body := cps_translate_term x x_cont_ann in
        let f_cont := KFix 0 [k_f_type] f_cont_body in
        let f_cont_ann := KAnnotated (KTForall 0 [k_f_type]) f_cont in
        cps_translate_term f f_cont_ann
    | TAbs body =>
        let k_body_type := ktypeof body in
        let new_continuation := KAnnotated (cps_translate_type_cont k_body_type) (KVar 0) in
        let k_body := cps_translate_term body new_continuation in
        let k_thunk := KFix 1 [] k_body in
        continue t k_thunk
    | TApp f type_arg =>
        let k_type_arg := cps_translate_type type_arg in
        let k_f_type := ktypeof f in
        let k_f_var := KAnnotated k_f_type (KVar 0) in
        let f_cont_body := KApp k_f_var [k_type_arg] [k] in
        let f_cont := KFix 0 [k_f_type] f_cont_body in
        let f_cont_ann := KAnnotated (KTForall 0 [k_f_type]) f_cont in
        cps_translate_term f f_cont_ann
    | Tuple terms =>
         (* k_var_list is [KVar n; KVar n - 1; ...; KVar 0], but with type annotations *)
        let k_var_list := fold_right (fun term ret =>
            let k_var := KVar (nat_as_var_ind (length ret)) in
            let k_var_ann := KAnnotated (ktypeof term) k_var in
            k_var_ann :: ret
        ) [] terms in
        let k_tuple := KAnnotated (ktypeof t) (KTuple k_var_list) in
        let k_term_base := KApp k [] [k_tuple] in
        let k_term_ind (term : Term) (prev : KTerm) : KTerm :=
            let k_term_ind_cont := KFix 0 [] prev in
            let k_term_ind_cont_ann := KAnnotated (ktypeof term) k_term_ind_cont in
            cps_translate_term term k_term_ind_cont_ann
        in
        fold_right k_term_ind k_term_base terms
    | ProjN i term =>
        let k_prod_type := ktypeof term in
        let k_proj_type := ktypeof t in
        let k_prod_var := KAnnotated k_prod_type (KVar 0) in
        let k_decl := KProjN i k_prod_var in
        let k_proj_var := KAnnotated k_proj_type (KVar 0) in
        let k_let_body := KApp k [] [k_proj_var] in
        let k_let := KLet k_decl k_let_body in
        let prod_cont := KFix 0 [k_prod_type] k_let in
        let prod_cont_ann := KAnnotated (KTForall 0 [k_prod_type]) prod_cont in
        cps_translate_term term prod_cont_ann
    | Op op a b =>
        let k_a_type := ktypeof a in
        let k_b_type := ktypeof b in
        let k_res_type := ktypeof t in
        let k_a_var := KAnnotated k_a_type (KVar 1) in
        let k_b_var := KAnnotated k_b_type (KVar 0) in
        let k_decl := KOp op k_a_var k_b_var in
        let k_res_var := KAnnotated k_res_type (KVar 0) in
        let k_let_body := KApp k [] [k_res_var] in
        let b_cont_body := KLet k_decl k_let_body in
        let b_cont := KFix 0 [k_b_type] b_cont_body in
        let b_cont_ann := KAnnotated (KTForall 0 [k_b_type]) b_cont in
        let a_cont_body := cps_translate_term b b_cont_ann in
        let a_cont := KFix 0 [k_a_type] a_cont_body in
        let a_cont_ann := KAnnotated (KTForall 0 [k_a_type]) a_cont in
        cps_translate_term a a_cont_ann
    | If0 cond then_case else_case =>
        let k_cond_type := ktypeof cond in
        let k_res_type := ktypeof t in
        let k_cond_var := KAnnotated k_cond_type (KVar 0) in
        let then_trans := cps_translate_term then_case k in
        let else_trans := cps_translate_term else_case k in
        let cond_cont_body := KIf0 k_cond_var then_trans else_trans in
        let cond_cont := KFix 0 [k_cond_type] cond_cont_body in
        let cond_cont_ann := KAnnotated (KTForall 0 [k_cond_type]) cond_cont in
        cps_translate_term cond cond_cont_ann
    end
.