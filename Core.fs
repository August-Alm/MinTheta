namespace MinTheta

module rec Core =

  open System.Collections.Generic

  let inline index (dep : int) (l : int) =
    if l < 0 then dep + l else l
  
  let inline level (len : int) (i : int) =
    len - i
  
  type Term =
    | Ref of string
    | Var of string * int
    | Lam of string * Term
    //| Fix of string * Term
    | App of Term * Term
    | Tht of string * Term
    | Ann of Term * Term
    | Chk of Term * Term
    | Star
  
  let rec adj (t : Term) =
    match t with
    | Ref _ -> t
    | Var _ -> t
    | Lam (x, t) -> Lam (x, adj t)
    | App (t, u) -> App (adj t, adj u)
    | Tht (x, t) -> Tht (x, adj t)
    | Ann (t, u) -> Chk (adj t, adj u)
    | Chk (t, u) -> Ann (adj t, adj u)
    | Star -> Star

  type Def =
    { Name : string
      Term : Term
      Type : Term
    }

  type Mod () =
    let defs = ResizeArray<Def> ()
    let refs = Dictionary<string, Hoas> ()
    member _.Defs = defs :> seq<Def>
    member _.GetDef x =
      defs
      |> Seq.tryFind (fun d -> d.Name = x)
      |> Option.defaultWith (fun () -> failwithf "undefined reference: %s" x)
    member _.GetType x =
      defs
      |> Seq.tryFind (fun d -> d.Name = x)
      |> Option.map (fun d -> d.Type)
      |> Option.defaultWith (fun () -> failwithf "undefined reference: %s" x)
    member _.AddDef def = defs.Add def
    member _.SetRef x t = refs[x] <- t
    member _.ContainsRef x = refs.ContainsKey x
    member _.GetRef x = refs[x]
    member _.TryGetRefState x = refs.TryGetValue x

  type Hoas =
    | HRef of string
    | HVar of string * int
    | HLam of string * (Hoas -> Hoas)
    //| HFix of string * (Hoas -> Hoas)
    | HApp of Hoas * Hoas
    | HTht of string * (Hoas -> Hoas) * (Hoas -> Hoas)
    | HAnn of Hoas * Hoas
    | HChk of Hoas * Hoas
    | HStar
  
  type Env = Hoas list

  let rec hoas (m : Mod) (env : Env) (t : Term) =
    match t with
    | Ref x ->
      if not (m.ContainsRef x) then
        match Seq.tryFind (fun d -> d.Name = x) m.Defs with
        | Some def -> m.SetRef x (hoas m env def.Term)
        | None -> failwithf "undefined reference: %s" x
      HRef x
    | Var (x, i) ->
      match List.tryItem (int i) env with
      | Some v -> v
      | None -> HVar (x, level env.Length i) 
    | Lam (x, t) -> HLam (x, fun u -> hoas m (u :: env) t)
    | App (t, u) -> HApp (hoas m env t, hoas m env u)
    | Tht (x, t) -> HTht (x, (fun u -> hoas m (u :: env) t), (fun u -> hoas m (u :: env) (adj t)))
    | Ann (t, u) -> HAnn (hoas m env t, hoas m env u)
    | Chk (t, u) -> HChk (hoas m env t, hoas m env u)
    | Star -> HStar
  
  let fresh (xs : string list) (x : string) =
    let rec go x = if List.contains x xs then go (x + "'") else x
    let x = go x
    let xs = x :: xs
    x, HVar (x, -(List.length xs)), xs
  
  let rec term (xs : string list) (t : Hoas) =
    match t with
    | HRef x -> Ref x
    | HVar (x, l) -> Var (x, index (List.length xs) l)
    | HLam (x, t) -> let x, xv, xs = fresh xs x in Lam (x, term xs (t xv))
    | HApp (t, u) -> App (term xs t, term xs u)
    | HTht (x, t, _) -> let x, xv, xs = fresh xs x in Tht (x, term xs (t xv))
    | HAnn (t, u) -> Ann (term xs t, term xs u)
    | HChk (t, u) -> Chk (term xs t, term xs u)
    | HStar -> Star
  
  // Alpha-eta equality. 
  let rec eq (m : Mod) dep t u =
    match t, u with
    | HRef x, HRef y -> x = y || eq m dep (m.GetRef x) (m.GetRef y) 
    | HRef x, u -> eq m dep (m.GetRef x) u
    | t, HRef y -> eq m dep t (m.GetRef y)
    | HVar (_, i), HVar (_, j) -> i = j
    | HLam (x, t), HLam (_, u) ->
      eq m (dep + 1) (t (HVar (x, dep))) (u (HVar (x, dep)))
    | HLam (x, t), u ->
      eq m (dep + 1) (t (HVar (x, dep))) (HApp (u, HVar (x, dep)))
    | t, HLam (y, u) ->
      eq m (dep + 1) (HApp (t, HVar (y, dep))) (u (HVar (y, dep)))
    | HApp (f, a), HApp (g, b) ->
      eq m dep f g && eq m dep a b
    | HTht (x, t, _), HTht (_, u, _) ->
      eq m (dep + 1) (t (HVar (x, dep))) (u (HVar (x, dep)))
    | HTht (x, t, _), u ->
      eq m (dep + 1) (t (HVar (x, dep))) (HAnn (HVar (x, dep), u))
    | t, HTht (y, u, _) ->
      eq m (dep + 1) (HAnn (HVar (y, dep), t)) (u (HVar (y, dep)))
    | HAnn (t, a), HAnn (u, b) ->
      eq m dep t u && eq m dep a b
    | HChk (t, a), HChk (u, b) ->
      eq m dep t u && eq m dep a b
    | HStar, HStar -> true
    | _ -> false
  
  
  let rec norm (m : Mod) (t : Hoas) =
    match t with
    | HRef x -> HRef x
    | HVar _ -> t
    | HLam (x, t) -> HLam (x, fun v -> norm m (t v))
    | HApp (HRef x, u) -> norm m (HApp (m.GetRef x, u))
    | HApp (t, u) ->
      match norm m t, norm m u with
      | HRef x, u -> norm m (HApp (m.GetRef x, u))
      | HLam (_, t), u -> norm m (t u)
      //| HTht (x, t), HLam (_, u) -> HTht (x, fun v -> norm m (HApp (t v, u v)))
      | HTht (x, t, tA), u -> HTht (x, (fun v -> norm m (HApp (t v, u))), fun v -> norm m (HApp (tA v, u)))// HAnn (v, u))))
      | t, u -> HApp (norm m t, norm m u)
    | HTht (x, t, tA) -> HTht (x, (fun v -> norm m (t v)), fun v -> norm m (tA v))
    | HAnn (t, u) ->
      match norm m t, norm m u with
      | t, HRef y -> norm m (HAnn (t, m.GetRef y))
      | t, HTht (_, _, u) -> norm m (u t)
      | t, HLam (y, u) -> HLam (y, fun v -> norm m (HAnn (HApp (t, v), u v)))
      //| HAnn (t, a), b when eq m 0 a b -> norm m (HAnn (t, b))
      //| HTht _ as t, HStar -> t
      //| HStar, HStar -> HStar
      | t, u -> HAnn (t, u)
    | HChk (t, u) ->
      match norm m t, norm m u with
      | t, HRef y -> norm m (HChk (t, m.GetRef y))
      | t, HTht (_, u, _) -> norm m (u t)
      | t, HLam (y, u) -> HLam (y, fun v -> norm m (HChk (HApp (t, v), u v)))
      //| HChk (t, a), b when eq m 0 a b -> norm m (HChk (t, b))
      | HAnn (t, a), b when eq m 0 a b -> norm m t
      | HRef x as r, b when eq m 0 (hoas m [] (m.GetType x)) b -> r
      | HTht _ as t, HStar -> t
      | HStar, HStar -> HStar
      | t, u -> HChk (t, u)
    | HStar -> HStar
  
  let eval m t = norm m (hoas m [] t)

  let quote t = term [] t

  /// Strong normalization.
  let normalize m t = quote (eval m t)

  let rec show (t : Term) =
    match t with
    | Ref x -> x
    | Var (x, _) -> x
    | Lam (x, t) -> $"λ{x}.{show t}"
    //| Fix (x, t) -> $"μ{x}.{show t}"
    | App (t, u) -> $"({show t} {show u})"
    | Tht (x, t) -> $"θ{x}.{show t}"
    | Ann (t, u) -> $"[{show t} : {show u}]"
    | Chk (t, u) -> $"[{show t} ⇓ {show u}]"
    | Star -> "✲"
  
  let check m (t : Term) (typ : Term) =
    let tNf = eval m t
    let tAnn = eval m (Chk (t, typ))
    if eq m 0 tNf tAnn then Ok (quote tNf)
    else Error (quote tNf, quote tAnn)
  

  let checkDef m (def : Def) =
    let trm = def.Term
    let typ = def.Type
    printfn "checking %s : %s" def.Name (show typ)
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

  let checkMod m = Seq.iter (checkDef m) m.Defs

