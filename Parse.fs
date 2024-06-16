namespace MinTheta

module Parse =

  module Input =

    [<AbstractClass>]
    type Input () =
      abstract member Pop : unit -> int32
      abstract member Peek : unit -> int32

    type InputOfString (str : string) =
      inherit Input ()
      let s = str
      let len = s.Length
      let mutable i = -1
      override _.Pop () =
        i <- i + 1; if i >= len then -1 else int s[i]
      override _.Peek () =
        let j = i + 1 in if j >= len then -1 else int s[j]

    type InputOfStream (strm : System.IO.StreamReader) =
      inherit Input ()
      override _.Pop () = strm.Read ()
      override _.Peek () = strm.Peek () 

  
  module Tokenizer =

    open Input
    open System.Text

    type Token =
      | T_Name of string 
      | T_Lam
      | T_Tht
      | T_Dot
      | T_LPar
      | T_RPar
      | T_LBra
      | T_RBra
      | T_Let of string
      | T_Eq
      | T_Sec
      | T_Eof
      | T_Col
      | T_Star
    
    let inline isAlpha c = (c > 64 && c < 91) || (c > 96 && c < 123)
    let inline isName c = isAlpha c || (c > 46 && c < 58) || c = int '_'
    let inline isHash c = (c = int '#')
    let inline isLF c = (c = int '\n')
    let inline isSpace c = (c = int ' ' || c = int '\t' || c = int '\r' || isLF c)

    let inline append (c : int) (sb : StringBuilder) =
      sb.Append (char c) |> ignore

    [<Struct>]
    type Position = { Line : int; Column : int }

    let inline error (pos : Position) msg =
      failwith (sprintf "At (%i, %i):\t%s" pos.Line pos.Column msg)

    type Tokenizer (inp : Input) =
      let sb = StringBuilder 32
      let mutable line = 1
      let mutable column = 0

      let rec readChar () =
        let mutable c = inp.Pop ()
        if isHash c then
          while not (isLF c) && c <> -1 do
            c <- inp.Pop ()
        if isLF c then
          line <- line + 1
          column <- 0
          readChar ()
        else
          column <- column + 1
          c
      
      let readNonSpace () =
        let mutable c = readChar ()
        while isSpace c do c <- readChar ()
        c

      let readName (c : int) =
        let mutable c = c
        let mutable cnxt = inp.Peek ()
        while isName cnxt do
          append c sb
          c <- readChar ()
          cnxt <- inp.Peek ()
        append c sb
        let name = sb.ToString ()
        sb.Clear () |> ignore
        name
      
      member _.ReadToken () =
        let c = readNonSpace ()
        let pos = {Line = line; Column = column}
        if c = -1 then
          pos, T_Eof
        else
          match char c with
          | 'λ' -> pos, T_Lam
          | 'θ' -> pos, T_Tht
          | '.' -> pos, T_Dot 
          | '(' -> pos, T_LPar
          | ')' -> pos, T_RPar
          | '[' -> pos, T_LBra
          | ']' -> pos, T_RBra
          | '@' -> pos, T_Let (readName (readNonSpace ()))
          | ';' -> pos, T_Sec
          | '=' -> pos, T_Eq
          | ':' -> pos, T_Col
          | '✲' -> pos, T_Star
          | _ ->
            if isName c then pos, T_Name (readName c)
            else error pos "Invalid token."


  open Core
  open Tokenizer

  let consume (tok : Token) (tokenizer : Tokenizer) =
    let pos, tok' = tokenizer.ReadToken ()
    if tok = tok' then ()
    else error pos $"expected {tok} but got {tok'}"
  
  type ParseEnv = {
    Vars : string list
    Bindings : Map<string, Term> }
  with
    static member empty = { Vars = []; Bindings = Map.empty }

  let boundOrRef (env : ParseEnv) (x : string) =
    match List.tryFindIndex ((=) x) env.Vars with
    | Some i -> Var (x, i)
    | None ->
      match Map.tryFind x env.Bindings with
      | Some t -> t
      | None -> Ref x
  
  let addVar (x : string) (env : ParseEnv) =
    { env with Vars = x :: env.Vars }
  
  let bind (x : string) (t : Term) (env : ParseEnv) =
    { env with Bindings = Map.add x t env.Bindings }

  let rec parse (tokenizer : Tokenizer) (env : ParseEnv) =
    match tokenizer.ReadToken () with
    | _, T_Lam ->
      match tokenizer.ReadToken () with
      | _, T_Name x ->
        consume T_Dot tokenizer
        let t = parse tokenizer (addVar x env)
        Lam (x, t)
      | pos, tok -> error pos $"expected name but got {tok}"
    | _, T_Tht ->
      match tokenizer.ReadToken () with
      | _, T_Name x ->
        consume T_Dot tokenizer
        let t = parse tokenizer (addVar x env)
        Tht (x, t)
      | pos, tok -> error pos $"expected name but got {tok}"
    | _, T_LBra ->
      let t = parse tokenizer env
      consume T_Col tokenizer
      let typ = parse tokenizer env
      consume T_RBra tokenizer
      Ann (t, typ)
    | _, T_LPar ->
      let t = parse tokenizer env
      let u = parse tokenizer env
      consume T_RPar tokenizer
      App (t, u)
    | _, T_Name x -> boundOrRef env x
    | _, T_Let x ->
      consume T_Eq tokenizer
      let t = parse tokenizer env
      consume T_Sec tokenizer
      parse tokenizer (bind x t env)
    | _, T_Star -> Star
    | pos, tok -> error pos $"syntax error; got {tok}"

  let parseName (tokenizer : Tokenizer) =
    match tokenizer.ReadToken () with
    | _, T_Name x -> x
    | pos, tok -> error pos $"expected name but got {tok}"

  let parseTerm (tokenizer : Tokenizer) =
    parse tokenizer ParseEnv.empty

  let parseDef x (tokenizer : Tokenizer) =
    consume T_Eq tokenizer
    let t = parseTerm tokenizer
    consume T_Col tokenizer
    let typ = parseTerm tokenizer
    { Name = x; Term = t; Type = typ }
  
  let parseMod (tokenizer : Tokenizer) =
    let m = Mod ()
    let rec go () =
      match tokenizer.ReadToken () with
      | _, T_Eof -> m
      | _, T_Let x ->
        m.AddDef (parseDef x tokenizer)
        go ()
      | pos, tok -> error pos $"expected '@ <name>' but got {tok}"
    go ()

  let parseTermFromString (str : string) =
    Input.InputOfString str
    |> Tokenizer 
    |> parseMod

  let parseModFromStream (strm : System.IO.StreamReader) =
    Input.InputOfStream strm
    |> Tokenizer 
    |> parseMod