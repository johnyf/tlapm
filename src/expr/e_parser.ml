(*
 * expr/parser.ml --- expressions (parsing)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open E_t
open Tla_parser.P
open Tla_parser
open Token

module Prop = Property

module Op = Optable
module B = Builtin

(*let b = ref false*)

let fixities =
  let fixities = Hashtbl.create 109 in
  let infix op prec assoc =
    Opr begin
      prec, Infix begin
        assoc, fun oploc a b ->
          let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Loc.merge (Util.get_locus a) (Util.get_locus b)) in
            Util.locate (Apply (op, [a ; b])) loc
      end
    end in
  let bin_prod =
    Opr begin
      (10, 13), Infix begin
        Left, fun oploc a b ->
          let loc = Loc.merge oploc (Loc.merge (Util.get_locus a) (Util.get_locus b)) in
            Util.locate begin
              match a.core with
                | Product es -> Product (es @ [b])
                | _ -> Product [a ; b]
            end loc
      end
    end in
  let prefix op prec =
    Opr begin
      prec, Prefix begin
        fun oploc a ->
          let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Util.get_locus a) in
            Util.locate (Apply (op, [a])) loc
      end
    end in
  let postfix op prec =
    Opr begin
      prec, Postfix begin
        fun oploc a ->
         let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Util.get_locus a) in
            Util.locate (Apply (op, [a])) loc
      end
    end
  in
    Hashtbl.iter begin
      fun form top ->
        Hashtbl.add fixities form begin
          match top.Op.defn with
            | _ -> begin
                let defn = match top.Op.defn with
                  | Some bltin -> Internal bltin
                  | None -> Opaque top.Op.name
                in match top.Op.fix with
                  | Op.Prefix -> prefix defn top.Op.prec
                  | Op.Postfix -> postfix defn top.Op.prec
                  | Op.Infix ass ->
                      infix defn top.Op.prec begin
                        match ass with
                          | Op.Left -> Left
                          | Op.Right -> Right
                          | Op.Non -> Non
                      end
                  | _ ->
                      failwith "Nonfix operator in optable?!"
              end
        end
    end Op.optable ;
    Hashtbl.replace fixities "\\X" bin_prod ;
    Hashtbl.replace fixities "\\times" bin_prod ;
    fixities

let distinct =
  let module S = Set.Make (String) in
  let rec check seen = function
    | [] -> true
    | v :: vs ->
        not (S.mem v.core seen)
        && check (S.add v.core seen) vs
  in
    fun vs -> check S.empty vs

let hint = locate anyident

let rec expr b = lazy begin
  resolve (expr_or_op b);
end

and expr_or_op b is_start =
  choice [
    (* labels *)
    if is_start then
      locate (attempt (use label) <**> use (expr b))
      <$> (function {core = (l, e)} as bl ->
             [ Atm (Parens (e, l) @@ bl) ])
    else fail "not a labelled expression" ;

    (* bulleted lists *)

    if is_start then
      locate (use (bulleted_list b))
      <$> (fun bl -> [Atm bl])
    else fail "not a bulleted list" ;

    (* temporal subscripting *)

    if is_start then
      attempt begin
        locate (prefix "[]" >>> punct "[" >*> use (expr b) <<< punct "]_" <**> use (sub_expr b))
        <$> begin
          fun { core = (e, v) ; props = props } ->
            [Atm { core = Tsub (Box, e, v) ; props = props }]
        end
      end
    else fail "not a [] [_]_" ;

    if is_start then
      attempt begin
        locate (prefix "<>" >>> punct "<<" >>> use (expr b) <<< punct ">>_" <*> use (sub_expr b))
        <$> begin
          fun { core = (e, v) ; props = props } ->
            [Atm { core = Tsub (Dia, e, v) ; props = props }]
        end
      end
    else fail "not a <> <<_>>_" ;

    (* ?fix operators *)

    attempt anyop >>+ begin fun p pts ->
      match Hashtbl.find_all fixities p with
        | [] -> fail ("unknown operator " ^ p)
        | ops ->
            let non_test = function
              | Opr (_, Infix (_, ix)) ->
                  attempt (punct "(" >>> (use (expr b) <*> (punct "," >>> use (expr b))) <<< punct ")")
                  (* <<! [Printf.sprintf "args of nonfix_%s" p] *)
                  <$> (fun (e, f) -> [P.Atm (ix pts e f)])
              | Opr (_, Postfix ix) ->
                  attempt (punct "(" >>> use (expr b) <<< punct ")")
                  (* <<! [Printf.sprintf "args of nonfix_%s" p] *)
                  <$> (fun e -> [P.Atm (ix pts e)])
              | _ -> fail "Unnonable"
            in
              choice (List.map non_test ops @ [return ops pts])
    end ;

    (* record fields *)
    if not is_start then
      attempt begin
        locate (punct "." >>> anyname)
      end <$> begin
        fun sw ->
          [ P.Opr begin
              (17, 17),
              P.Postfix begin
                fun _ r ->
                  let loc = Loc.merge (Util.get_locus r) (Util.get_locus sw) in
                    Util.locate (Dot (r, sw.core)) loc
              end
            end ]
      end
    else fail "not a rproj" ;

    (* function arguments *)

    if not is_start then
      attempt begin
        locate (punct "[" >>> sep1 (punct ",") (use (expr b)) <<< punct "]")
      end
      <$> begin
        fun esw ->
          [ P.Opr begin
              (17, 17),
              P.Postfix begin
                fun oploc f ->
                  let loc = Loc.merge (Util.get_locus f) (Util.get_locus esw) in
                    Util.locate (FcnApp (f, esw.core)) loc
              end
            end ]
      end
    else fail "not a farg" ;

    (* nonfix operators *)

    if is_start then
      locate begin
        attempt (use (operator b))
        <*> use (opargs b)
        <*> optional (use (subref b))
      end <$> begin
        fun prs ->
          let ((op, args), sr) = prs.core in
          let e = match args with
            | [] -> op
            | _ -> Apply (op, args) @@ prs
          in match sr, op.core with
            | None, Opaque x when x.[0] = '<' ->
               (* A step name is more like an empty subref than an ident. *)
               [ P.Atm (Bang (e, []) @@ prs) ]
            | None, _ -> [ P.Atm e ]
            | Some sr, _ -> [ P.Atm (Bang (e, sr) @@ prs) ]
      end
    else fail "not an opapp" ;

    (* complex expressions *)

    use (complex_expr b) <$> (fun e -> [P.Atm e]) ;
  ]

and label = lazy begin
  locate begin
    anyident <*> choice [
      punct "(" >>> sep1 (punct ",") (locate anyident) <<< punct ")" ;
      succeed [] ;
    ] <<< punct "::"
    <$> (fun (l, ns) -> Nlabel (l, ns))
  end
end

and opargs b = lazy begin
  optional begin
    punct "(" >*> sep1 (punct ",") (use (oparg b)) <<< punct ")"
  end <$> Option.default []
end

and subref b = lazy begin
  punct "!" >*> sep1 (punct "!") (use (sel b))
end

and sel b = lazy begin
  choice [
    choice [ anyident ; anyop ] <**> optional (punct "(" >>> sep1 (punct ",") (use (oparg b)) <<< punct ")")
    <$> (fun (l, args) -> match args with
           | None -> Sel_lab (l, [])
           | Some args -> Sel_lab (l, args)) ;

    punct "(" >*> sep1 (punct ",") (use (oparg b)) <<< punct ")"
    <$> (fun args -> Sel_inst args) ;

    nat <$> (fun n -> Sel_num n) ;

    punct "<<" <!> Sel_left ;

    punct ">>" <!> Sel_right ;

    punct ":" <!> Sel_down ;

    punct "@" <!> Sel_at ;
  ]
end

and complex_expr b = lazy begin
  choice [
    (* IF ... THEN ... ELSE *)

    locate begin
      (kwd "IF" >*> use (expr b))
      <**> (kwd "THEN" >>> use (expr b))
      <**> (kwd "ELSE" >>> use (expr b))
    end <$> begin
      fun ({core = ((a, b), c)} as ite) ->
        { ite with core = If (a, b, c) }
    end ;

    (* LET ... IN ... *)

    locate begin
      kwd "LET" >*> star1 (use (defn b))
      <**> (kwd "IN" >>> use (expr b))
    end <$> begin
      fun ({core = (ds, e)} as letin) ->
        { letin with core =  Let (ds, e) }
    end;

    (* use sequent <$> (fun sq -> Sequent sq) ; *)

    (* quantifiers *)

    (* constant quantification
    for example:
        \E x, y, z:  x = y
        \E x \in S, <<y, z>> \in A \X B:  x = y

    Read Section 16.1.1 on pages 293--294 of the book "Specifying Systems",
    in particular page 294.

    The definitions of (bounded) tuple declarations in quantifiers are:

    \E <x1, ..., xk>> \in S:  p ==
        \E x1, ..., xk:
            /\ <<x1, ..., xk>> \in S
            /\ p

    \A <x1, ..., xk>> \in S:  p ==
        \A x1, ..., xk:
            \/ <<x1, ..., xk>> \notin S
            \/ p
    *)
    locate begin
      choice [ punct "\\A" <!> Forall ;
               punct "\\E" <!> Exists ;
             ]
      <**> alt [
            use (func_boundeds b) ;
            use (unboundeds b)
                <$> (fun bs -> ([bs], [[]]))
            ]
      <**> (punct ":" >>> use (expr b))
    end <$> begin
      fun ({core = ((q, (bs, letin)), e)} as quant) ->
        let core = make_quantifier_from_tuple q bs letin e in
        { quant with core = core }
    end ;

    locate begin
      choice [ punct "\\AA" <!> Forall ;
               punct "\\EE" <!> Exists ]
      <**> (sep1 (punct ",") hint <?> distinct)
      <**> (punct ":" >>> use (expr b))
    end <$> begin
      fun ({core = ((q, vs), e)} as tquant) ->
        { tquant with core = Tquant (q, vs, e) }
    end ;

    (* CHOOSE expressions

    examples:
        CHOOSE x:  TRUE
        CHOOSE x \in S:  TRUE
        CHOOSE <<x, y>> \in S:  TRUE

    Read Section 16.1.2 on pages 294--296 of the book "Specifying Systems",
    in particular page 296.

    The definition of a tuple declaration in
    CHOOSE expressions is:

    CHOOSE <<x1, ..., xn>>:  p ==
        CHOOSE y:
            \E x1, ..., xn:
                /\ y = <<x1, ..., xn>>
                /\ p
    *)
    locate begin
      kwd "CHOOSE"
        >*> alt [
            (* declared identifier or tuple (unbouned) *)
            hint
                <*> (punct ":" >>> use (expr b))
                <$> begin
                    fun (v, e) -> Choose (v, None, e)
                    end;

            (* unbounded tuple *)
            (punct "<<" >>> (sep (punct ",") hint) <<< punct ">>")
                <*> (punct ":" >>> use (expr b))
                <$> begin fun (vs, e) ->
                    let name = (List.hd vs).core in
                    let v = noprops ("fcnbnd#" ^ name) in
                    let hd = (v, Constant, No_domain) in
                    let bounds = [hd] in
                    let letin =
                        List.mapi begin
                        fun i op ->
                            let e =
                                let f = noprops (Opaque v.core) in
                                let idx =
                                    let i_str = string_of_int (i + 1) in
                                    let num = Num (i_str, "") in
                                    noprops num in
                                let e_ = FcnApp (f, [idx]) in
                                noprops e_ in
                            let defn_ = Operator (op, e) in
                            noprops defn_
                        end vs in
                    make_choose_from_tuple [bounds] [letin] e
                    end
            ;

            (* bounded declared identifier or tuple *)
            use (func_boundeds b)
                <**> (punct ":" >>> use (expr b))
                <$> begin
                    fun  ((bs, letin), e) ->
                    make_choose_from_tuple bs letin e
                    end
            ]
    end;

    locate begin
      kwd "CASE"
      >*> sep1 (prefix "[]") (use (expr b) <**> (punct "->" >>> use (expr b)))
      <*> optional (prefix "[]" >*> kwd "OTHER" >*> punct "->" >*> use (expr b))
    end <$> begin
      fun ({core = (arms, oth)} as case) ->
        { case with core = Case (arms, oth) }
    end ;

    use (atomic_expr b);
  ]
end


and atomic_expr b = lazy begin
  choice [
    locate begin
      (* set constructor *)
      punct "{" >>>
        choice [
          (* axiom scheme of separation
          for example:
              {x \in S:  x + 1}
              {<<x, y>> \in S:  x = y}

          The definition of a (bounded) tuple declaration in
          the axiom scheme of separation is:

          {<<x1, ..., xn>> \in S:  p} ==
            {y \in S:
                \E x1, ..., xn:
                    /\ y = <<x1, ..., xn>>
                    /\ p

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 301
          *)
          attempt (use (func_boundeds b))
            <*> (punct ":" >*> use (expr b))
            <$> begin
                fun ((bs, letin), e) ->
                    make_setst_from_tuple bs letin e
                end
          ;

          (* axiom scheme of replacement
          for example:  {x + 1:  x \in S}

          The definition of (bounded) tuple declarations in
          the axiom scheme of replacement is:

          {e:  <<x1, ..., xn>> \in S} ==
            {
                (LET
                    z == CHOOSE <<x1, ..., xn>>:  y = <<x1, ..., xn>>
                    x1 == z[1]
                    ...
                    xn == z[n]
                IN
                    e):  y \in S}

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 301
          *)
          attempt (use (expr b)<<< punct ":")
            <*> use (func_boundeds b)
            <$> begin
                fun (e, (bs, letin)) ->
                make_setof_from_tuple bs letin e
                end
          ;

          (* set enumeration
          for example:  {1, 2, 3}

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 300
          *)
          sep (punct ",") (use (expr b))
          <$> (fun es -> SetEnum es)
        ]
      <<< punct "}"
    end ;

    locate begin
      punct "[" >>>
        choice [
          (* Record constructor:  [name1 |-> e1, ...] *)
          enabled (anyname <<< punct "|->") >*>
            sep1 (punct ",") (anyname <<< punct "|->" <**> use (expr b))
          <<< punct "]"
          <$> (fun fs -> Record fs) ;

          (* Set of records:  [name1: Values1, ...] *)
          enabled (anyname <<< punct ":") >*>
            sep1 (punct ",") (anyname <<< punct ":" <*> use (expr b))
          <<< punct "]"
          <$> (fun fs -> Rect fs) ;

          (* EXCEPT expression, examples:

          [f EXCEPT ![1] = 2]
          [f EXCEPT ![1] = 3, ![2] = 4]
          [f EXCEPT ![1, 2] = 3]
          [f EXCEPT !["a"] = 3, !["b"] = 4]
          [f EXCEPT !.a = 3, !.b = 4]
          [f EXCEPT !.a = 3, !["b"] = 4]
          *)
          begin
            let rec exspec b = lazy begin
              (* except equality, examples:

              ![1] = 2
              !["a"] = 2
              !.a = 2
              ![1, 2] = 3
              *)
              punct "!" >>> use (trail b) <<< infix "=" <*> (use (expr true))
              (* choice [ attempt (punct "@" <!> At true);  use expr ] *)
            end
            and trail b = lazy begin
              star1 begin
                choice [
                  (* field reference:  .name *)
                  punct "." >>> anyname <$> (fun x -> Except_dot x) ;
                  (* application, examples:

                  [arg]
                  [arg1, arg2]
                  *)
                  punct "[" >>> alt [
                        (* single expression within square brackets:  [arg] *)
                        (use (expr b)) <<< punct "]";
                        (* comma-separated list of expressions,
                        within square brackets:  [arg1, ..., argN] *)
                        (sep1 (punct ",") (use (expr b)))
                            <$> (fun es -> noprops (Tuple es))
                            <<< punct "]"
                    ]
                    <$> (fun e -> Except_apply e) ;
                ]
              end
            end in
              attempt (use (expr b) <<< kwd "EXCEPT")
              <**> sep1 (punct ",") (use (exspec b)) <<< punct "]"
              <$> (fun (e, xs) -> Except (e, xs))
          end ;

          (* Function constructor, examples:

          [x \in S |-> e]
          [<<x, y>> \in S \X R |-> e]
          [<<x, y>> \in S \X R, z \in Q |-> e]

          Only bounded declarations are allowed in function constructors.
          Read 16.1.7 on pages 301--304 of the book "Specifying Systems",
          in particular pages 303--304.
          *)
          attempt (use (func_boundeds b) <<< punct "|->")
              <**> use (expr b)
              <<< punct "]"
              <$> make_func_from_boundeds_expr
          ;

          use (expr b) >>= begin fun e ->
            choice [
              (* Set of functions:  [Domain -> Range] *)
              punct "->" >*> use (expr b) <<< punct "]"
              <$> (fun f -> Arrow (e, f)) ;

              (* Box action operator:  [A]_e *)
              punct "]_" >>> use (sub_expr b)
              <$> (fun v -> Sub (Box, e, v)) ;
            ]
          end ;
        ]
    end ;

    locate begin
      punct "<<" >>>
        sep (punct ",") (use (expr b)) >>= begin
          function
            | [e] ->
                choice [
                  punct ">>_" >*> use (sub_expr b)
                  <$> (fun v -> Sub (Dia, e, v)) ;

                  punct ">>" <!> Tuple [e] ;
                ]
            | es ->
                punct ">>" <!> Tuple es
        end
    end ;

    locate begin
      punct "WF_" >*>
        use (sub_expr b) <**> optional (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) ->
               match e with
                 | Some ex -> Fair (Weak, v, ex)
                 | None ->
                     begin match v.core with
                       | Bang (a,sr) -> let srev = List.rev sr in
                           begin match List.hd srev with
                             | Sel_lab (h,el) -> (*if List.length el = 1 then*)
                                 Fair (Weak, (Bang(a, (List.rev ((Sel_lab(h,[]))::(List.tl srev)))) @@ v), List.hd el)
                             | _ -> Errors.bug ~at:v "Expr.Parser.WF:1"
                           end
                       | _ -> Errors.set v "Expr.Parser.WF:2"; failwith "Expr.Parser.WF:2"
                     end
             )
    end ;

    locate begin
      punct "SF_" >*>
        use (sub_expr b) <**> optional (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) ->
               match e with
                 | Some ex -> Fair (Strong, v, ex)
                 | None ->
                     begin match v.core with
                       | Bang (a,sr) -> let srev = List.rev sr in
                           begin match List.hd srev with
                             | Sel_lab (h,el) -> (*if List.length el = 1 then*)
                                 Fair (Strong, (Bang(a, (List.rev ((Sel_lab(h,[]))::(List.tl srev)))) @@ v), List.hd el)
                             | _ -> Errors.bug ~at:v "Expr.Parser.SF:1"
                           end
                       | _ -> Errors.set v "Expr.Parser.SF:2"; failwith "Expr.Parser.SF:2"
                     end
             )
    end ;
(*        use (sub_expr b) <**> (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) -> Fair (Strong, v, e))
    end ;*)

    locate begin
      punct "@" <!> (At b)
    end ;

    use (reduced_expr b) ;
  ]
end

and reduced_expr b = lazy begin
  choice [
    (* parentheses *)
    punct "(" >>> use (expr b) <<< punct ")"
    <$> (fun e -> Parens (e, Syntax @@ e) @@ e) ;

    (* string *)
    locate begin
      scan begin
        function
          | STR s -> Some (String s)
          | _ -> None
      end
    end ;

    (* number *)
    locate begin
      scan begin
        function
          | NUM (m, n) -> Some (Num (m, n))
          | _ -> None
      end
    end ;

    locate (kwd "TRUE" <!> Internal B.TRUE) ;
    locate (kwd "FALSE" <!> Internal B.FALSE) ;
    locate (kwd "BOOLEAN" <!> Internal B.BOOLEAN) ;
    locate (kwd "STRING" <!> Internal B.STRING) ;

    (* locate (punct "@" <!> At) ; *)
  ]
end

and sub_expr b = lazy begin
  choice [
    locate begin
      hint <*> optional (use (subref b))
    end <$> begin
      fun prs ->
        let (id, sr) = prs.core in
        let e = Opaque id.core @@ id in
        match sr with
          | None -> e
          | Some sr -> Bang (e, sr) @@ prs
    end ;

    use (atomic_expr b) ;
  ]
end

and bull_at bull where =
  P.scan begin
    fun t ->
      let module Loc = Loc in
        if t.Token.form = OP bull && Loc.column t.Token.loc.Loc.start = where
        then Some ()
        else None
  end

and bulleted_list b = lazy begin
  lookahead (scan begin
               function
                 | OP "/\\" -> Some "/\\"
                 | OP "\\/" -> Some "\\/"
                 | _ -> None
             end)
  >>+ fun bt loc ->
    get >>= fun px ->
      let module Loc = Loc in
      let bwhere = Loc.column loc.Loc.start in
      let newledge = { px with ledge = Loc.column loc.Loc.start + 1 } in
        star1 (bull_at bt bwhere >>> using newledge (use (expr b)))
        <$> (fun es -> match bt with
               | "\\/" -> List (Or, es)
               | _     -> List (And, es))
end

and operator b = lazy begin
  choice [
    locate begin
      kwd "LAMBDA" >*> sep1 (punct ",") hint
      <**> (punct ":" >>> use (expr b))
      <$> (fun (vs, e) -> Lambda (List.map (fun v -> (v, Shape_expr)) vs, e))
    end ;

    locate begin
      choice [
        anyident ;
        scan begin
            function
              | ST (`Num n, l, 0) -> Some (Printf.sprintf "<%d>%s" n l)
              | _ -> None
        end ;
      ] <$> (fun v -> Opaque v)
    end ;

    punct "(" >>> use (operator b) <<< punct ")" ;
  ]
end


and make_quantifier_from_tuple quant ys letin e = begin
    let mem_op, bool_op =
        match quant with
        | Exists -> noprops (Internal Mem), And
        | Forall -> noprops (Internal Notmem), Or in
    let juncts = List.map2
        (fun ybnds letin_xs ->
            match letin_xs with
            | [] -> begin
                match List.hd ybnds with
                | _, _, Domain dom -> begin
                    let last_dom = ref dom in
                    List.map
                    (fun ybnd ->
                        let y, dom = match ybnd with
                            | y, _, Domain dom ->
                                last_dom := dom;
                                y, dom
                            | y, _, Ditto ->
                                y, !last_dom
                            | _, _, No_domain ->
                                assert false in
                        let y_expr = noprops (Opaque y.core) in
                        let operands = [y_expr; dom] in
                        let apply_ = Apply (mem_op, operands) in
                        noprops apply_)
                    ybnds
                    end
                | _, _, No_domain -> []
                | _, _, Ditto -> assert false
                end
            | _ ->
                let dom = match ybnds with
                    | [(_, _, Domain dom)] -> dom
                    | _ -> assert false in
                let xs_hints = List.map
                    (fun df ->
                        match df.core with
                        | Operator (name, _) -> name
                        | _ -> assert false)
                    letin_xs in
                let xs_exprs = List.map
                    (fun x -> noprops (Opaque x.core))
                    xs_hints in
                let xs_tuple = noprops (Tuple xs_exprs) in
                let mem =
                    let exprs = [xs_tuple; dom] in
                    let apply_ = Apply (mem_op, exprs) in
                    noprops apply_ in
                [mem])
        ys letin in
    let juncts = List.concat juncts in
    let juncts = e :: juncts in
    let junction = noprops (List (bool_op, juncts)) in
    let constant_decls = List.map2
        (fun ybnds letin_xs ->
            match letin_xs with
            | [] -> ybnds
            | _ ->
                List.map
                    (fun df ->
                            match df.core with
                            | Operator (name, _) ->
                                (name, Constant, No_domain)
                            | _ -> assert false)
                    letin_xs)
        ys letin in
    let constant_decls = List.concat constant_decls in
    Quant (quant, constant_decls, junction)
end


and make_setof_from_tuple ys letin e =
    let e = make_let_for_setof_from_tuple ys letin e in
    SetOf (e, List.concat ys)


and make_func_from_tuple ys letin e =
    let e = make_let_for_setof_from_tuple ys letin e in
    Fcn (List.concat ys, e)


and make_let_for_setof_from_tuple ys letin e = begin
    let defs = List.map2
        (fun ybnds letin_xs ->
            match letin_xs with
            | [] -> []
            | _ -> begin
            let y = match ybnds with
                | [(y, _, Domain _)] -> y
                | _ -> assert false in
            let y_identifier = noprops (Opaque y.core) in
            let z_name = y.core ^ "#" ^ "choose" in
            let z_hint = noprops z_name in
            let z_identifier = noprops (Opaque z_name) in
            let z_def =
                let e =
                    let eq = noprops (Internal Eq) in
                    let xs_exprs = List.map
                        (fun df ->
                            match df.core with
                            | Operator (name, _) ->
                                noprops (Opaque name.core)
                            | _ -> assert false)
                        letin_xs in
                    let xs_tuple = noprops (Tuple xs_exprs) in
                    let operands = [y_identifier; xs_tuple] in
                    let apply_ = Apply (eq, operands) in
                    noprops apply_ in
                let (z_bnd: E_t.bound) = (z_hint, Constant, No_domain) in
                let choose_ = make_choose_from_tuple
                    [[z_bnd]] [letin_xs] e in
                let def_ = Operator (z_hint, noprops choose_) in
                noprops def_ in
            let x_defs = List.mapi
                (fun i df ->
                    match df.core with
                    | Operator (name, _) ->
                        let idx =
                            let i_str = string_of_int (i + 1) in
                            let num = Num (i_str, "") in
                            noprops num in
                        let e_ = FcnApp (z_identifier, [idx]) in
                        let op_expr = noprops e_ in
                        let defn_ = Operator (name, op_expr) in
                        noprops defn_
                    | _ -> assert false)
                letin_xs in
            z_def :: x_defs
            end)
        ys letin in
    let defs = List.concat defs in
    match defs with
    | [] -> e
        (* no `LET...IN` needed, because no tuple declarations
        appear in the function constructor, for example:

        [x \in S |-> x + 1]

        is represented with `bs` containing the declaration
        `x \in S`, and `e` the expression `x + 1`.
        *)
    | _ ->
        let letin_ = Let (defs, e) in
        noprops letin_
        (* insert a `LET...IN`, needed to represent tuple
        declarations, for example:

        [<<x, y>> \in S,  r, w \in Q |-> x + y - r - w]

        is represented with `bs` containing the declarations
        `fcnbnd#x \in S`, `r \in Q`, `w \in Ditto`, and
        `e` the expression

            LET
                x == fcnbnd#x[1]
                y == fcnbnd#x[2]
            IN
                x + y - r - w
        *)
end


and make_choose_from_tuple
        (ys: E_t.bounds list)
        (letin: E_t.defn list list)
        (e: E_t.expr) = begin
    assert ((List.length ys) = 1);
    let y, dom =
        let ybnd = List.hd ys in
        match ybnd with
        | [(y, _, Domain dom)] -> y, Some dom
        | [(y, _, No_domain)] -> y, None
        | _ -> assert false in
    let expr = make_single_quantifier_from_tuple
        y letin e in
    Choose (y, dom, expr)
end


and make_setst_from_tuple ys letin e = begin
    assert ((List.length ys) = 1);
    let y, dom =
        let ybnd = List.hd ys in
        match ybnd with
        | [(y, _, Domain dom)] -> y, dom
        | _ -> assert false in
    let expr = make_single_quantifier_from_tuple
        y letin e in
    SetSt (y, dom, expr)
end


and make_single_quantifier_from_tuple y letin e = begin
    assert ((List.length letin) = 1);
    let letin_xs = List.hd letin in
    match letin_xs with
    | [] -> e
    | _ ->
        let xs_hints = List.map
            (fun df ->
                match df.core with
                | Operator (name, _) -> name
                | _ -> assert false)
            letin_xs in
        let xs_quantifier_bounds = List.map
            (fun x -> (x, Constant, No_domain))
            xs_hints in
        let xs_exprs = List.map
            (fun x -> noprops (Opaque x.core))
            xs_hints in
        let xs_tuple = noprops (Tuple xs_exprs) in
        let eq =
            let exprs = [
                noprops (Opaque y.core);
                xs_tuple] in
            let apply_ = Apply (
                noprops (Internal Eq),
                exprs) in
            noprops apply_ in
        let exprs = [eq; e] in
        let quantified_expr = noprops (List (And, exprs)) in
        noprops (Quant (
            Exists, xs_quantifier_bounds, quantified_expr))
end


(* The function `bounds` is currently unused.

The function `bounds` allows including both bounded and unbounded
declarations in a single constructor.

Including both bounded and unbounded declarations in a single
quantifier constructor is not allowed in TLA+,
read Section 16.1.1 on pages 293--294 of the book "Specifying Systems",
in particular page 294.

Including unbounded declarations in a function constructor or
function definition is not allowed in TLA+,
read Section 16.1.7 on pages 301--304 of the book "Specifying Systems",
in particular pages 303--304.

Including unbounded declarations in a set constructor is
not allowed in TLA+,
read Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
in particular page 301.
*)
and bounds b = lazy begin
  sep1 (punct ",") (sep1 (punct ",") hint <*> optional (infix "\\in" >*> use (expr b)))
  <$> begin
    fun bss ->
      let vss = List.map begin
        fun (vs, dom) -> match dom with
          | None ->
              List.map (fun v -> (v, Constant, No_domain)) vs
          | Some dom ->
              (List.hd vs, Constant, Domain dom)
              :: List.map (fun v -> (v, Constant, Ditto)) (List.tl vs)
      end bss in
      List.concat vss
  end
end


(* The function `unboundeds` parses a list of only unbounded declarations. *)
and unboundeds b = lazy begin
    sep1 (punct ",") hint
    <$> begin
        fun vs ->
        List.map (fun v -> (v, Constant, No_domain)) vs
        end
end


(* The function `boundeds` parses a list of only bounded declarations. *)
and boundeds b = lazy begin
  sep1 (punct ",") (sep1 (punct ",") hint <*> (infix "\\in" >*> use (expr b)))
  <$> begin
    fun bss ->
      let vss = List.map begin
        fun (vs, dom) ->
          (List.hd vs, Constant, Domain dom)
          :: List.map (fun v -> (v, Constant, Ditto)) (List.tl vs)
      end bss in
      List.concat vss
  end
end


and make_func_from_boundeds_expr ((bs, letin), e) =
    (* decide whether to insert a `LET...IN`
    for representing bound identifiers described by bounded
    tuples in the source
    *)
    make_func_from_tuple bs letin e


(* comma-separated listed of declarations within function constructor *)
and func_boundeds b = lazy begin
    (* comma-separated list of declarations, examples:

    m \in S
    a, b \in R
    m \in S,  a, b \in R
    m \in S,  a, b \in R,  <<x, y>> \in A \X B
    *)
    sep1 (punct ",") (choice [
        (* bounded constants, examples:

        m \in S
        a, b \in R
        *)
        (sep1 (punct ",") hint <*> (infix "\\in" >*> use (expr b)))
            <$> begin
                fun (vs, dom) ->
                    let bounds =
                        let hd = (List.hd vs, Constant, Domain dom) in
                        let tl = List.map
                            (fun v -> (v, Constant, Ditto)) (List.tl vs) in
                        hd :: tl in
                    let letin = [] in
                    (bounds, letin)
            end;
        (* bounded tuples of constants, examples:

        <<x, y>> \in S
        <<a, b, c >> \in A \X B \X C

        A function constructor is represented with `Fcn`,
        which takes `bounds` as first argument.
        `bounds` represents a list of bound identifiers (constants here).

        So the tuples need to be converted to individual identifier bounds.
        This is done by introducing intermediate definitions in a `LET...IN`.
        Each bounded tuple (like `<<x, y>>` above) is replaced by a fresh
        identifier of the form:

            fcnbnd#first_name

        where "first_name" results from using the first identifier
        that occurs within the tuple. For example, `<<x, y>>` is replaced by

            fcnbnd#x

        The fresh identifier is used inside the `LET...IN` for defining each
        of the identifiers that occurred within the tuple. For example,
        `[<<x, y>> \in S |-> ...]` becomes:

            [fcnbnd#x \in S:
                LET
                    x == fcnbnd#x[1]
                    y == fcnbnd#x[2]
                IN
                    ...]

        The hashmark is used within the identifier fcnbnd#... to ensure that
        the fresh identifier is different from all other identifiers in the
        current context, without the need to inspect the context (which is
        not available while parsing). The syntax of TLA+ ensures this,
        because no identifier in TLA+ source can contain a hashmark.

        In each function constructor, the first identifier from the tuple
        (like "x" above) is unique, because the TLA+ syntax ensures that
        each identifier is unique within its context. Therefore, each bounded
        tuple within a function constructor will be replaced by a unique
        fresh identifier (unique within that context and that context's
        extensions).
        *)
        ((punct "<<" >>> (sep (punct ",") hint) <<< punct ">>")
            <*> (infix "\\in" >*> use (expr b)))
            <$> begin
                fun (vs, dom) ->
                    (* bounds *)
                    (* name of first identifier that appears within the tuple,
                    for example "x" from the tuple `<x, y>`.
                    This name is to be used as suffix of the fresh identifier
                    that will represent the tuple.
                    *)
                    let name = (List.hd vs).core in
                    (* fresh identifier that will represent the tuple,
                    for example "fcnbnd#x" from the tuple `<x, y>`
                    *)
                    let v = noprops ("fcnbnd#" ^ name) in
                    (* bounded constant declaration for the fresh identifier,
                    for example `fcnbnd#x \in S` from `<x, y> \in S`
                    *)
                    let hd = (v, Constant, Domain dom) in
                    (* a list with a single element, in preparation for
                    later concatenation
                    *)
                    let bounds = [hd] in
                    (* `LET...IN` definitions

                    We now create the definitions of the identifiers that
                    appeared inside the tuple declaration, using in the
                    definiens the fresh identifier `v` that has just been
                    introduced.

                    For example, the tuple declaration `<<x, y>> \in S`
                    would here result in the creation of two definitions:

                        x == fcnbnd#x[1]
                        y == fcnbnd#x[2]
                    *)
                    let letin =
                        (* create one definition for each identifier that
                        appears inside the tuple declaration
                        *)
                        List.mapi begin
                        fun i op ->  (* arguments:
                            - `i` is the 0-based index of the tuple element
                            - `op` is the tuple element (an identifier)
                            *)
                            let e =
                                (* tuple identifier, for example "fcnbnd#x" *)
                                let f = noprops (Opaque v.core) in
                                (* 1-based index numeral *)
                                let idx =
                                    let i_str = string_of_int (i + 1) in
                                    let num = Num (i_str, "") in
                                    noprops num in
                                (* function application on the index,
                                for example:  fcnbnd#x[1]
                                *)
                                let e_ = FcnApp (f, [idx]) in
                                noprops e_ in
                            (* definition for `op`, for example:

                            x == fcnbnd#x[1]

                            The result is of type `defn`.
                            *)
                            let defn_ = Operator (op, e) in
                            noprops defn_
                        end vs in
                    (* Bundle the constant declarations of fresh
                    identifiers (in `bounds`) and the definitions (in terms of
                    these fresh identifiers) of the identifiers that appeared
                    in the tuple declaration (these definitions are in `letin`).

                    These definitions are used at the call site to construct
                    a new `LET...IN` expression that wraps the function's
                    value expression (the `e` in `[... |-> e]`).

                    The declarations are used, together with this `LET...IN`
                    expression, to populate a function constructor `Fcn`.
                    *)
                    (bounds, letin)
            end
        ])
    <$> begin
      fun bss ->
        (* Unzip the two lists.
        `bss` is a list of pairs of lists, so `bounds` is a list of lists
        and so is `letin`.
        *)
        let (
            (bounds: E_t.bounds list),
            (letin: E_t.defn list list)) = List.split bss in
        (* Flatten each list of lists into a list.
        At this point we return:
        - `bounds`: a list of lists of bounds that will be used in a `Fcn`,
          and
        - `letin`: a (possibly empty) list of lists of operator definitions
          that will be used (if nonempty) to form a `Let` that will wrap the
          expression that defines the value of the function in `Fcn`.
        These returned values are used also for set constructors or
        constant quantifier constructors.
        *)
        (bounds, letin)
    end
end


(* pragmas *)

and float =
  number <$> (fun (m, n) ->
                float_of_string (Printf.sprintf "%s.%s0" m n))


and read_method_by = lazy begin
  ident "by" >>> use read_method_args <$> (fun l -> l)
end

(* FIXME remove this syntax; for the moment, treat it like "by" *)
and read_method_set = lazy begin
  ident "set" >>> use read_method_args <$> (fun l -> l)
end

and read_new_method = lazy begin
  pragma (star (choice [use read_method_by; use read_method_set]))
end

and read_method_args = lazy begin
    punct "(" >*> sep1 (punct ";") (use (read_method_arg)) <<< punct ")"
end

and read_method_arg = lazy begin
      hint <*> (punct ":" >*> use string_or_float_of_expr)
end


and string_val = lazy begin
  str <$> fun s -> Bstring s
end

and float_val = lazy begin
  float <$> fun s -> Bfloat s
end

and expr_def = lazy begin
   punct "@" <!> Bdef
end

and string_or_float_of_expr = lazy begin
  choice [ use string_val;
           use expr_def;
           use float_val;
         ]
end




(* definitions *)

and defn b = lazy begin
  locate (use (ophead b) <<< punct "==") >>= fun ({core = head} as oph) ->
    commit begin
      choice [
        locate (use (instance b))
        <$?> (fun i ->
                match head with
                | `Op (h, args) ->
                    let args = List.map fst args in
                    let loc = Loc.merge (Util.get_locus oph) (Util.get_locus i) in
                      Some (Util.locate (Instance (h, { i.core with inst_args = args })) loc)
                | _ ->
                    None) ;

        (* ajout *)

        use (expr b) <*> optional (use read_new_method) <$>
          begin
          fun (e,o) ->
            let loc = Loc.merge (Util.get_locus oph) (Util.get_locus e) in
            let op =
              match o with
                | Some (l) ->
                    begin
                      match head with
                        | `Op (h, args) ->
                            begin
                              match args with
                                | [] -> Bpragma (h, e, l)
                                | _ -> Bpragma (h,
                                                (Util.locate (Lambda (args, e)) loc),
                                                l)
                            end
                        | `Fun (h, args) ->  assert false (*** FIXME add error message ***)
                    end
                | None ->
                    begin
                      match head with
                        | `Op (h, args) ->
                            begin
                              match args with
                                | [] -> Operator (h, e)
                                | _ -> Operator (h, Util.locate (Lambda (args, e)) loc)
                            end
                        | `Fun (h, args) ->
                            begin
                            let f = make_func_from_boundeds_expr
                                (args, e) in
                            Operator (h, Util.locate f loc)
                            end
                    end
            in Util.locate op loc
          end;

(*        use (expr b) <$> begin
          fun e ->
            let loc = Loc.merge (Util.get_locus oph) (Util.get_locus e) in
            let op = match head with
              | `Op (h, args) -> begin
                  match args with
                    | [] -> Operator (h, e)
                    | _ -> Operator (h, Util.locate (Lambda (args, e)) loc)
                end
              | `Fun (h, args) ->
                  Operator (h, Util.locate (Fcn (args, e)) loc)
            in Util.locate op loc
        end ;*)
      ]
    end
end

and ophead b = lazy begin
  choice [
    (* prefix operator definition *)
    locate anyprefix <*> hint <$> (fun (h, u) -> `Op (h, [u, Shape_expr])) ;
    hint >>= fun u ->
      choice [
        (* postfix operator definition *)
        locate anypostfix <$> (fun h -> `Op (h, [u, Shape_expr])) ;

        (* infix operator definition *)
        locate anyinfix <*> hint <$> (fun (h, v) -> `Op (h, [u, Shape_expr ; v, Shape_expr])) ;

        (* function definition
        for example:
            f[x \in S, y \in Q] == ...
            f[<<x, y>> \in S \X Q, r \in T] == ...

        Only bounded declarations are allowed in function constructors.
        Read 16.1.7 on pages 301--304 of the book "Specifying Systems",
        in particular pages 303--304.

        This is why the function `func_boundeds` is called,
        instead of the function `bounds`.
        (Calling  the function `boundeds` would be correct,
        but would not parse tuple declarations within function
        definitions.)
        *)
        punct "[" >>> use (func_boundeds b) <<< punct "]"
        <$> (fun args -> `Fun (u, args)) ;

        (* first-order-operator definition *)
        optional (punct "(" >>> sep1 (punct ",") ((use opdecl)) <<< punct ")")
        <$> (function
               | None -> `Op (u, [])
               | Some args -> `Op (u, args)) ;

      ] ;
  ]
end

and opdecl = lazy begin
  choice [
    locate anyprefix <<< punct "_"
    <$> (fun h -> (h, Shape_op 1)) ;

    punct "_" >*>
      choice [
        locate anypostfix
        <$> (fun h -> (h, Shape_op 1)) ;

        locate anyinfix <<< punct "_"
        <$> (fun h -> (h, Shape_op 2))
      ] ;

    hint <*> optional (punct "(" >>> sep1 (punct ",") (punct "_") <<< punct ")")
    <$> begin
      fun (h, args) -> match args with
        | None -> (h, Shape_expr)
        | Some args ->
            (h, Shape_op (List.length args))
    end ;
  ]
end

and oparg b = lazy begin
  alt [
    use (expr b);

    locate anyop
    <$> (fun op ->
           if Hashtbl.mem Optable.optable op.core then
             let top = Hashtbl.find Optable.optable op.core in
             match top.Optable.defn with
               | Some bin -> { op with core = Internal bin }
               | None -> { op with core = Opaque op.core }
           else { op with core = Opaque op.core }) ;
  ]
end

and instance b = lazy begin
  kwd "INSTANCE" >*> anyident
  <*> optional (kwd "WITH" >*> use (subst b))
  <$> (fun (m, sub) ->
         { inst_args = [] ;
           inst_mod = m ;
           inst_sub = Option.default [] sub })
end

and subst b = lazy begin
  let exprify op = return (Opaque op) in
  sep1 (punct ",")
    (choice [ hint ; locate anyop ]
     <**> (punct "<-" >>> choice [ use (expr b) ; locate (anyop >>+ exprify) ]))
end

and hyp b = lazy begin locate begin
  choice [
    optional (kwd "NEW") >>= begin fun nk ->
      choice [
        kwd "VARIABLE" >*> hint <$> (fun v -> (Flex v)) ;
        choice [
          kwd "STATE" <!> State ;
          kwd "ACTION" <!> Action ;
          kwd "TEMPORAL" <!> Temporal ;
          (if Option.is_some nk then
             optional (kwd "CONSTANT") <!> 1
           else
             kwd "CONSTANT" <!> 2) <!> Constant ;
        ] <**> alt [ hint <*> (infix "\\in" >*> use (expr b)) <$> (fun (v, b) -> (v, Shape_expr, Bounded (b, Visible))) ;
                     (use opdecl) <$> (fun (v, shp) -> (v, shp, Unbounded)) ]
        <$> (fun (lev, (v, shp, ran)) -> (Fresh (v, shp, lev, ran))) ;
      ]
    end ;

    locate (optional (hint <<< punct "::") <*> use (expr_or_sequent b))
    <$> begin
      fun le -> match le.core with
        | (None, e) -> Fact (e, Visible, NotSet)
        | (Some l, e) -> Fact (Parens (e, Xlabel (l.core, []) @@ l) @@ le,
        Visible, NotSet)
    end ;
  ]
end end

and sequent b = lazy begin
  kwd "ASSUME" >*> sep1 (punct ",") (use (hyp b))
  <**> (kwd "PROVE" >>> use (expr b))
  <$> (fun (hs, e) -> { context = Deque.of_list hs ; active = e }) ;
end

and expr_or_sequent b = lazy begin
  alt [
    use (expr b) ;
    locate (use (sequent b)) <$> (fun sq -> { sq with core = Sequent sq.core }) ;
  ]
end
