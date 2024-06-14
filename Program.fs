namespace MinTheta

module Program =

  open Core
  open Parse
  open Parse.Input
  open Parse.Tokenizer
  open System.IO

  [<EntryPoint>]
  let main argv =
    use stream = new FileStream(argv[0], FileMode.Open, FileAccess.Read, FileShare.Read)
    use reader = new StreamReader(stream)
    let tokenizer = Tokenizer (InputOfStream reader)
    let m = parseMod tokenizer
    for KeyValue (_, def) in m do
      checkAndReport m def.Term def.Type
    1