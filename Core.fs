namespace MinTheta

module rec Core =

  let inline index (dep : int) (l : int) =
    if l < 0 then dep + l else l
  
  let inline level (len : int) (i : int) =
    len - i
  
  type Term =
    | Ref of string
    | Var of string * int
    | Lam of string * Term
    | App of Term * Term
    | Tht of string * Term
    | Ann of Term * Term
    | Star
  
  type Def = { Name : string; Term : Term; Type : Term }

  type Mod = Map<string, Def>
  
  type Hoas =
    | HRef of HDef
    | HVar of string * int
    | HLam of string * (Hoas -> Hoas)
    | HApp of Hoas * Hoas
    | HTht of string * (Hoas -> Hoas)
    | HAnn of Hoas * Hoas
    | HStar
  
  type HDef = { Name : string; HTerm : Hoas; HType : Hoas }

  type Env = Hoas list

  let rec hoas (m : Mod) (env : Env) (t : Term) =
    match t with
    | Ref x ->
      match Map.tryFind x m with
      | Some def -> HRef (hoasDef m env def)
      | None -> failwithf "undefined reference: %s" x
    | Var (x, i) ->
      match List.tryItem (int i) env with
      | Some v -> v
      | None -> HVar (x, level env.Length i) 
    | Lam (x, t) -> HLam (x, fun u -> hoas m (u :: env) t)
    | App (t, u) -> HApp (hoas m env t, hoas m env u)
    | Tht (x, t) -> HTht (x, fun u -> hoas m (u :: env) t)
    | Ann (t, u) -> HAnn (hoas m env t, hoas m env u)
    | Star -> HStar
  
  and hoasDef (m : Mod) (env : Env) (def : Def) =
    { Name = def.Name
      HTerm = hoas m env def.Term
      HType = hoas m env def.Type }
  
  let fresh (xs : string list) (x : string) =
    let rec go x = if List.contains x xs then go (x + "'") else x
    let x = go x
    let xs = x :: xs
    x, HVar (x, -(List.length xs)), xs
  
  let rec term (xs : string list) (t : Hoas) =
    match t with
    | HRef def -> Ref def.Name
    | HVar (x, l) -> Var (x, index (List.length xs) l)
    | HLam (x, t) -> let x, xv, xs = fresh xs x in Lam (x, term xs (t xv))
    | HApp (t, u) -> App (term xs t, term xs u)
    | HTht (x, t) -> let x, xv, xs = fresh xs x in Tht (x, term xs (t xv))
    | HAnn (t, u) -> Ann (term xs t, term xs u)
    | HStar -> Star

  // Definitional equality.
  let rec eq dep t u =
    match t, u with
    | HRef dt, HRef du -> eq dep dt.HTerm du.HTerm
    | HVar (_, i), HVar (_, j) -> i = j
    | HLam (x, t), HLam (_, u) ->
      eq (dep + 1) (t (HVar (x, dep))) (u (HVar (x, dep)))
    | HLam (x, t), u ->
      eq (dep + 1) (t (HVar (x, dep))) (HApp (u, HVar (x, dep)))
    | t, HLam (y, u) ->
      eq (dep + 1) (HApp (t, HVar (y, dep))) (u (HVar (y, dep)))
    | HApp (f, a), HApp (g, b) ->
      eq dep f g && eq dep a b
    | HTht (x, t), HTht (_, u) ->
      eq (dep + 1) (t (HVar (x, dep))) (u (HVar (x, dep)))
    | HTht (x, t), u ->
      eq (dep + 1) (t (HVar (x, dep))) (HAnn (HVar (x, dep), u))
    | t, HTht (y, u) ->
      eq (dep + 1) (HAnn (HVar (y, dep), t)) (u (HVar (y, dep)))
    | HAnn (t, a), HAnn (u, b) ->
      eq dep t u && eq dep a b
    | HStar, HStar -> true
    | _ -> false  
  
  let rec norm (t : Hoas) =
    match t with
    | HRef def -> norm def.HTerm
    | HVar _ -> t
    | HLam (x, t) -> HLam (x, fun v -> norm (t v))
    | HApp (t, u) ->
      match norm t, norm u with
      | HLam (_, t), u -> t u
      | HTht (x, t), u -> HTht (x, fun v -> norm (HApp (t v, u)))
      | t, u -> HApp (t, u)
    | HTht (x, t) -> HTht (x, fun v -> norm (t v))
    | HAnn (t, u) ->
      match norm t, norm u with
      | t, HTht (_, u) -> u t
      | HLam (x, t), HLam (_, u) -> HLam (x, fun v -> norm (HAnn (t v, u v)))
      | HLam (x, t), HStar -> HLam (x, fun v -> norm (HAnn (t v, HStar)))
      | t, HLam (y, u) -> HLam (y, fun v -> norm (HAnn (t, u v)))
      | HAnn (t, a) as ta, b -> if eq 0 a b then norm t else HAnn (ta, b)
      | HTht _ as t, HStar -> t
      | t, u -> HAnn (t, u)
    | HStar -> HStar
  
  let eval m t = norm (hoas m [] t)

  let quote t = term [] t

  /// Strong normalization.
  let normalize m t = quote (eval m t)

  let rec show (t : Term) =
    match t with
    | Ref x -> x
    | Var (x, _) -> x
    | Lam (x, t) -> $"λ{x}.{show t}"
    | App (t, u) -> $"({show t} {show u})"
    | Tht (x, t) -> $"θ{x}.{show t}"
    | Ann (t, u) -> $"[{show t} : {show u}]"
    | Star -> "✲"
  
  let check m (t : Term) (typ : Term) =
    let tNf = eval m t
    let tAnn = eval m (Ann (t, typ))
    if eq 0 tNf tAnn then Ok (quote tNf)
    else Error (quote tNf, quote tAnn)
  
  let checkAndReport m (trm : Term) (typ : Term) =
    match check m trm typ with
    | Ok t ->
      [ "all good!"
        $"term: {show trm}"
        $"normalized type: {show (normalize m typ)}"
        $"normalized term: {show t}\n" ]
      |> String.concat "\n\t"
      |> printfn "%s"
    | Error (t, tAnn) ->
      [ "type error!"
        $"term: {show trm}"
        $"normalized type: {show (normalize m typ)}"
        $"normalized term: {show t}"
        $"annotated term: {show tAnn}\n" ]
      |> String.concat "\n\t"
      |> printfn "%s"



module Library =

  open Core

  let any = Tht ("t", Var ("t", 0))

  let hom =
    Lam ("a", Lam ("b", Tht ("f", Lam ("x",
      let a = Var ("a", 3)
      let b = Var ("b", 2)
      let f = Var ("f", 1)
      let x = Var ("x", 0)
      Ann (App (f, Ann (x, a)), b)))))
  
  let map =
    Lam ("a", Lam ("b", Tht ("f", Lam ("x",
      let a = Var ("a", 3)
      let b = Var ("b", 2)
      let f = Var ("f", 2)
      let x = Var ("x", 0)
      Ann (App (f, Ann (x, a)), App (b, x))))))

  let ind =
    Lam ("a", Lam ("b", Tht ("f", Lam ("x",
      let a = Var ("a", 3)
      let b = Var ("b", 2)
      let f = Var ("f", 1)
      let x = Var ("x", 0)
      Ann (App (f, Ann (x, a)), App (App (b, f), x))))))
  
  let endo =
    Lam ("a", App (App (hom, Var ("a", 0)), Var ("a", 0)))

  let nat =
    Lam ("f", Lam ("g", Lam ("a",
      let fa = App (Var ("f", 2), Var ("a", 0))
      let ga = App (Var ("g", 1), Var ("a", 0))
      App (App (hom, fa), ga))))

  let church = App (App (nat, endo), endo)

  let two = Lam ("s", Lam ("z", App (Var ("s", 1), App (Var ("s", 1), Var ("z", 0)))))
  let two_ = Lam ("_", two)
