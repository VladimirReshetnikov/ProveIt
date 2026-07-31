-- | Rendering Djex candidate terms as Lean 4 syntax (the \"out of the
-- engine\" direction of SYNTHESIS_PROPOSAL.md \'s translator).
--
-- The rendering is deliberately universe-agnostic: anonymous constructors
-- (@\10216a, b\10217@, @\10216\10217@), leading-dot injections (@.inl@\/@.inr@), @match@,
-- and @nomatch@ all elaborate against both the @Prop@ spellings
-- (@And@\/@Or@\/@Iff@\/@False@\/@True@) and the @Type@ spellings
-- (@Prod@\/@Sum@\/@Empty@\/@Unit@), because every candidate is elaborated by
-- the Lean backend against the fully known goal type before display.
--
-- Djinn's Haskell model differs from Lean in two ways this module has to
-- bridge structurally, by fitting the candidate to the goal fragment:
--
--   * quantifiers are implicit for Djinn, so its terms never bind them;
--     'fit' weaves an anonymous binder for every explicit quantifier the
--     goal reaches while the candidate is still binding (including inside
--     tuple components, injections, and match alternatives), and
--     eta-expands cores left under an explicit quantifier - always for
--     introduction forms, and as an extra variant for elimination forms
--     (which may instead be transported whole);
--   * instantiating a quantified hypothesis is silent for Djinn, while
--     Lean's explicit binders need @_@ placeholders.  An /applied/
--     hypothesis is unambiguous: placeholders are woven into the argument
--     list wherever the hypothesis type's spine has an explicit
--     quantifier (@h a q@ over @A \8594 \8704 b, b \8594 C@ renders @h a _ q@).  A
--     use whose /trailing/ quantifiers may or may not be instantiated
--     (a bare occurrence, or an application consuming only the arrows
--     before them) is genuinely ambiguous, so such occurrence sites are
--     enumerated into textual variants (each site kept or instantiated)
--     and the caller's backend verification keeps the first variant that
--     elaborates.
--
-- The engine is never trusted (design rule 2): a rendering failure just
-- drops the candidate, and everything shown has been verified.
module Leant.Synth.Render
  ( renderLeanTerm
  ) where

import Data.List (intercalate, nub, sortOn, subsequences)
import qualified Data.Map.Strict as Map

import Language.Haskell.Synthesis.Generated
  ( Expression (..)
  , Pattern (..)
  )
import Language.Haskell.Synthesis.Name
  ( Boxity (Boxed)
  , Name
  , SpecialName (TupleConstructor)
  , nameSpecial
  , nameSpelling
  )

import Leant.Synth.Fragment (Frag (..), Slot (..), fragSpine, leadingTypeArgs)

-- | Render one candidate expression against the goal fragment.  Returns
-- a nonempty group of textual variants, best guess first; the caller
-- verifies them in order and keeps the first that elaborates.
renderLeanTerm :: Frag -> Expression String -> Either String [String]
renderLeanTerm goalFrag expr0 = do
  base <- uniquify (normalizeExpr 0 expr0)
  texts <- concat <$> mapM variantsFor
    (nub [fit force goalFrag base 0 [] | force <- [False, True]])
  case nub texts of
    [] -> Left "no renderable variant"
    group -> Right (take 12 group)
 where
  variantsFor (expr, _, domPairs) = do
    let doms = Map.fromList domPairs
        sites = countSites doms expr
        sets
          | sites == 0 = [[]]
          | sites <= 3 = siteSubsets sites
          | otherwise = [[], [0 .. sites - 1]]
    mapM (\set -> render doms 0 (markSites doms set expr)) sets

-- | Instantiation subsets, transport-first: no site instantiated, all
-- sites, then the mixed subsets by size.
siteSubsets :: Int -> [[Int]]
siteSubsets k = [] : full : sortOn (\s -> (length s, s)) middle
 where
  full = [0 .. k - 1]
  middle =
    [ s | s <- subsequences full, not (null s), length s /= k ]

-- Globals -------------------------------------------------------------------

data GlobalKind = GInl | GInr | GUnit

globalKind :: Name -> Either String GlobalKind
globalKind name
  | nameSpelling name == Just "Left" = Right GInl
  | nameSpelling name == Just "Right" = Right GInr
  | nameSpecial name == Just (TupleConstructor Boxed 0) = Right GUnit
  | otherwise = Left ("unexpected global in candidate: " ++ show name)

-- Pattern normalization ------------------------------------------------------
--
-- Lean 4 has no as-patterns and its @fun@\/@let@ binder patterns must be
-- irrefutable, so before rendering:
--   * every @As x p@ becomes a plain binding of @x@ plus an inner
--     @match x with | p => ...@ around the body;
--   * a constructor pattern in @fun@\/@let@ position becomes a fresh
--     binder plus an inner @match@.
-- Fresh binders use reserved spellings (@\"$synth0\"@, ...) that the later
-- uniquification pass renames along with everything else.

splitAs :: Pattern String -> (Pattern String, [(String, Pattern String)])
splitAs pat = case pat of
  As x p -> (Bind x, [(x, p)])
  Constructor n ps ->
    let (ps', obs) = unzip (map splitAs ps)
    in (Constructor n ps', concat obs)
  TuplePattern ps ->
    let (ps', obs) = unzip (map splitAs ps)
    in (TuplePattern ps', concat obs)
  other -> (other, [])

-- irrefutable and therefore usable directly as a fun/let binder pattern
binderSimple :: Pattern String -> Bool
binderSimple pat = case pat of
  Bind _ -> True
  Wildcard -> True
  TuplePattern ps -> all binderSimple ps
  _ -> False

wrapObligations :: [(String, Pattern String)] -> Expression String
                -> Expression String
wrapObligations obs body =
  foldr (\(x, p) b -> Case (Local x) [(p, b)]) body obs

normalizeExpr :: Int -> Expression String -> Expression String
normalizeExpr fresh expr = case expr of
  Local _ -> expr
  Global _ -> expr
  Hole _ -> expr
  Apply f a -> Apply (normalizeExpr fresh f) (normalizeExpr fresh a)
  Tuple es -> Tuple (map (normalizeExpr fresh) es)
  Lambda pats body ->
    let step (i, done, wrap) pat =
          let (pat', obs) = splitAs pat
          in if binderSimple pat'
               then (i, done ++ [pat'], wrap . wrapObligations obs)
               else
                 let v = freshName i
                 in ( i + 1
                    , done ++ [Bind v]
                    , wrap . wrapObligations ((v, pat') : obs)
                    )
        (fresh', pats', wrapAll) = foldl step (fresh, [], id) pats
    in Lambda pats' (normalizeExpr fresh' (wrapAll body))
  Let pat rhs body ->
    let (pat', obs) = splitAs pat
        rhs' = normalizeExpr fresh rhs
    in if binderSimple pat'
         then Let pat' rhs' (normalizeExpr fresh (wrapObligations obs body))
         else
           let v = freshName fresh
           in Let (Bind v) rhs'
                (normalizeExpr (fresh + 1)
                  (wrapObligations ((v, pat') : obs) body))
  Case scrut alts ->
    let alt (pat, body) =
          let (pat', obs) = splitAs pat
          in (pat', normalizeExpr fresh (wrapObligations obs body))
    in Case (normalizeExpr fresh scrut) (map alt alts)
 where
  freshName i = "$synth" ++ show i

-- Uniquification -------------------------------------------------------------
--
-- Djinn's binder identities are strings of its own choosing; rename every
-- binding site to a fresh Lean-safe name (scoped, so shadowing in the
-- source term stays correct).  The name pool leaves @z1, z2, ...@ free
-- for binders introduced later by 'fit'.

nameSupply :: [String]
nameSupply =
  ["a", "b", "c", "d", "e", "f", "g", "h", "p", "q", "r", "u", "v", "w"]
    ++ ["x" ++ show n | n <- [1 :: Int ..]]

type Ren = Map.Map String String

uniquify :: Expression String -> Either String (Expression String)
uniquify expr0 = fst <$> go Map.empty 0 expr0
 where
  go :: Ren -> Int -> Expression String
     -> Either String (Expression String, Int)
  go env n expr = case expr of
    Local x -> case Map.lookup x env of
      Just x' -> Right (Local x', n)
      Nothing -> Left ("unbound local in candidate: " ++ x)
    Global _ -> Right (expr, n)
    Hole _ -> Left "candidate contains an unfilled hole"
    Apply f a -> do
      (f', n1) <- go env n f
      (a', n2) <- go env n1 a
      Right (Apply f' a', n2)
    Tuple es -> do
      (es', n') <- goList env n es
      Right (Tuple es', n')
    Lambda pats body -> do
      (pats', env', n1) <- goPats env n pats
      (body', n2) <- go env' n1 body
      Right (Lambda pats' body', n2)
    Let pat rhs body -> do
      (rhs', n1) <- go env n rhs
      (pats', env', n2) <- goPats env n1 [pat]
      (body', n3) <- go env' n2 body
      case pats' of
        [pat'] -> Right (Let pat' rhs' body', n3)
        _ -> Left "internal: let pattern arity"
    Case scrut alts -> do
      (scrut', n1) <- go env n scrut
      (alts', n2) <- goAlts env n1 alts
      Right (Case scrut' alts', n2)

  goAlts _ n [] = Right ([], n)
  goAlts env n ((pat, body) : rest) = do
    (pats', env', n1) <- goPats env n [pat]
    (body', n2) <- go env' n1 body
    (rest', n3) <- goAlts env n2 rest
    case pats' of
      [pat'] -> Right ((pat', body') : rest', n3)
      _ -> Left "internal: alt pattern arity"

  goList _ n [] = Right ([], n)
  goList env n (x : xs) = do
    (x', n1) <- go env n x
    (xs', n2) <- goList env n1 xs
    Right (x' : xs', n2)

  goPats env n [] = Right ([], env, n)
  goPats env n (p : ps) = do
    (p', env1, n1) <- goPat env n p
    (ps', env2, n2) <- goPats env1 n1 ps
    Right (p' : ps', env2, n2)

  goPat env n pat = case pat of
    Wildcard -> Right (Wildcard, env, n)
    Bind x ->
      let name = nameSupply !! n
      in Right (Bind name, Map.insert x name env, n + 1)
    TuplePattern ps -> do
      (ps', env', n') <- goPats env n ps
      Right (TuplePattern ps', env', n')
    Constructor c ps -> do
      (ps', env', n') <- goPats env n ps
      Right (Constructor c ps', env', n')
    As _ _ -> Left "internal: as-pattern survived normalization"

-- Fitting the candidate to the goal fragment ---------------------------------
--
-- 'fit' walks the goal fragment and the candidate together, threading a
-- counter for fresh eta binders and an accumulator of (binder, domain
-- fragment) pairs for every binder whose domain the goal determines.
-- With @force@, cores left under an explicit quantifier are eta-expanded
-- even when they are elimination forms (the non-forced fit transports
-- those whole; both variants are offered to verification).

fit :: Bool -> Frag -> Expression String -> Int
    -> [(String, Frag)] -> (Expression String, Int, [(String, Frag)])
fit force frag expr n doms =
  let (pats, core) = lambdaSpine expr
      (pats', remaining, doms1, exhausted) = walk frag pats doms
      (etaPats, core1, coreFrag, n1)
        | exhausted && (force || introCore core)
            && spineHasExplicitAll remaining =
            etaExpand remaining core n
        | otherwise = ([], core, remaining, n)
      (core2, n2, doms2) = fitCore force coreFrag core1 n1 doms1
      allPats = pats' ++ etaPats
  in (if null allPats then core2 else Lambda allPats core2, n2, doms2)
 where
  lambdaSpine (Lambda ps b) =
    let (more, coreExpr) = lambdaSpine b in (ps ++ more, coreExpr)
  lambdaSpine e = ([], e)

  -- an implicit quantifier costs no binder, so peel it even after the
  -- candidate's binders run out - otherwise the fragment handed on is
  -- the quantifier rather than the connective underneath it, and the
  -- body never gets fitted at all
  walk (FAll False _ rest) ps ds = walk rest ps ds
  walk f [] ds = ([], f, ds, True)
  walk (FArr dom rest) (p : ps) ds =
    let (ps', f', ds', ex) = walk rest ps (bindDomainPairs p dom ++ ds)
    in (p : ps', f', ds', ex)
  walk (FAll True _ rest) ps ds =
    let (ps', f', ds', ex) = walk rest ps ds
    in (Wildcard : ps', f', ds', ex)
  walk f ps ds = (ps, f, ds, False)

  introCore e = case e of
    Tuple _ -> True
    Global _ -> True
    Apply h _ -> introCore h
    _ -> False

  spineHasExplicitAll f = SlotAll True `elem` fragSpine f

  etaExpand f core k = case f of
    FArr _ rest ->
      let name = "z" ++ show k
          (ps, core', f', k') =
            etaExpand rest (Apply core (Local name)) (k + 1)
      in (Bind name : ps, core', f', k')
    FAll True _ rest ->
      let (ps, core', f', k') = etaExpand rest core k
      in (Wildcard : ps, core', f', k')
    FAll False _ rest -> etaExpand rest core k
    _ -> ([], core, f, k)

-- | Recurse through introduction forms whose component types the goal
-- fragment determines, and through match alternatives (branches produce
-- the scrutinized position's type; sum\/product eliminations also reveal
-- the branch binders' domains when the scrutinee is a known binder,
-- whose quantifiers - instantiated silently by the engine before the
-- case split - are peeled first).
fitCore :: Bool -> Frag -> Expression String -> Int
        -> [(String, Frag)] -> (Expression String, Int, [(String, Frag)])
fitCore force cf ce n ds = case (cf, ce) of
  (FProd a b, Tuple [x, y]) ->
    let (x', n1, ds1) = fit force a x n ds
        (y', n2, ds2) = fit force b y n1 ds1
    in (Tuple [x', y'], n2, ds2)
  (FSum a _, Apply h@(Global g) x) | isKind GInl g ->
    let (x', n1, ds1) = fit force a x n ds in (Apply h x', n1, ds1)
  (FSum _ b, Apply h@(Global g) x) | isKind GInr g ->
    let (x', n1, ds1) = fit force b x n ds in (Apply h x', n1, ds1)
  (_, Case scrut alts) ->
    let scrutFrag = case scrut of
          Local s -> peelAlls <$> lookup s ds
          _ -> Nothing
        goAlt (done, k, dss) (pat, body) =
          let branchDoms = case (scrutFrag, pat) of
                (Just (FSum a _), Constructor g [p])
                  | Right GInl <- globalKind g -> bindDomainPairs p a
                (Just (FSum _ b), Constructor g [p])
                  | Right GInr <- globalKind g -> bindDomainPairs p b
                (Just f, TuplePattern _) -> bindDomainPairs pat f
                (Just f, Bind x) -> [(x, f)]
                _ -> []
              (body', k', dss') = fit force cf body k (branchDoms ++ dss)
          in (done ++ [(pat, body')], k', dss')
        (alts', n1, ds1) = foldl goAlt ([], n, ds) alts
    in (Case scrut alts', n1, ds1)
  (_, Let pat rhs body) ->
    let (body', n1, ds1) = fit force cf body n ds
    in (Let pat rhs body', n1, ds1)
  _ -> (ce, n, ds)
 where
  isKind k g = case (globalKind g, k) of
    (Right GInl, GInl) -> True
    (Right GInr, GInr) -> True
    _ -> False
  peelAlls (FAll _ _ b) = peelAlls b
  peelAlls f = f

-- | Binders whose domain type the goal fragment determines, recursing
-- through tuple destructuring.
bindDomainPairs :: Pattern String -> Frag -> [(String, Frag)]
bindDomainPairs (Bind x) dom = [(x, dom)]
bindDomainPairs (TuplePattern [p, q]) (FProd a b) =
  bindDomainPairs p a ++ bindDomainPairs q b
bindDomainPairs _ _ = []

-- Ambiguous instantiation sites ----------------------------------------------
--
-- A use of a quantified hypothesis whose type still has leading explicit
-- quantifiers after the supplied term arguments may be a transport of
-- the remaining pi type or an instantiation at a type the elaborator
-- must infer.  Such sites are numbered (in one fixed traversal order)
-- and 'markSites' tags a chosen subset for instantiation; the tag is a
-- reserved character no binder name can contain.

instTag :: String
instTag = "\1"

tagged :: String -> Bool
tagged = (instTag ==) . take 1

stripTag :: String -> String
stripTag x = if tagged x then drop 1 x else x

-- | Trailing explicit quantifiers of @frag@ once @k@ term arguments have
-- been consumed (with @k = 0@ this is 'leadingTypeArgs').
trailingAlls :: Frag -> Int -> Int
trailingAlls frag 0 = leadingTypeArgs frag
trailingAlls (FAll _ _ rest) k = trailingAlls rest k
trailingAlls (FArr _ rest) k = trailingAlls rest (k - 1)
trailingAlls _ _ = 0

countSites :: Map.Map String Frag -> Expression String -> Int
countSites doms expr = snd (markOrCount doms [] expr 0)

markSites :: Map.Map String Frag -> [Int] -> Expression String
          -> Expression String
markSites doms set expr = fst (markOrCount doms set expr 0)

-- | One traversal serving both passes: numbers each ambiguous site and
-- rewrites the chosen ones to tagged names.
markOrCount :: Map.Map String Frag -> [Int] -> Expression String -> Int
            -> (Expression String, Int)
markOrCount doms set = go
 where
  go expr i = case expr of
    Local x -> site x [] i (\x' -> Local x')
    Apply _ _ ->
      let (headExpr, args) = spine expr []
          goArgs [] j = ([], j)
          goArgs (a : as) j =
            let (a', j1) = go a j
                (as', j2) = goArgs as j1
            in (a' : as', j2)
      in case headExpr of
        Local x ->
          let (args', i1) = goArgs args i
          in site x args' i1 (\x' -> foldl Apply (Local x') args')
        _ ->
          let (h', i1) = go headExpr i
              (args', i2) = goArgs args i1
          in (foldl Apply h' args', i2)
    Tuple es ->
      let (es', i') = goMany es i in (Tuple es', i')
    Lambda pats body ->
      let (body', i') = go body i in (Lambda pats body', i')
    Let pat rhs body ->
      let (rhs', i1) = go rhs i
          (body', i2) = go body i1
      in (Let pat rhs' body', i2)
    Case scrut alts ->
      let (scrut', i1) = go scrut i
          goAlt (pat, body) j =
            let (body', j') = go body j in ((pat, body'), j')
          (alts', i2) = foldl
            (\(done, j) alt -> let (alt', j') = goAlt alt j
                               in (done ++ [alt'], j'))
            ([], i1) alts
      in (Case scrut' alts', i2)
    Global _ -> (expr, i)
    Hole _ -> (expr, i)

  goMany [] i = ([], i)
  goMany (e : es) i =
    let (e', i1) = go e i
        (es', i2) = goMany es i1
    in (e' : es', i2)

  site x args i rebuild = case Map.lookup x doms of
    Just frag | trailingAlls frag (length args) > 0 ->
      ( rebuild (if i `elem` set then instTag ++ x else x)
      , i + 1
      )
    _ -> (rebuild x, i)

  spine (Apply f a) acc = spine f (a : acc)
  spine f acc = (f, acc)

-- Rendering ------------------------------------------------------------------
--
-- Precedence levels: 0 = open (fun/match/let/nomatch), 1 = application,
-- 2 = atom.  A subterm rendered in a position requiring a higher level is
-- parenthesized.  @doms@ maps quantified-hypothesis binders to their
-- domain fragments: applications weave @_@ placeholders through the
-- argument list wherever the type's spine has an explicit quantifier,
-- and tagged occurrences additionally instantiate their trailing
-- quantifiers.

render :: Map.Map String Frag -> Int -> Expression String
       -> Either String String
render doms = go
 where
  go :: Int -> Expression String -> Either String String
  go req expr = case expr of
    Local x -> renderUse req x []
    Global name -> do
      kind <- globalKind name
      case kind of
        GUnit -> Right (at req 2 "\10216\10217")
        GInl -> Right (at req 0 ".inl")
        GInr -> Right (at req 0 ".inr")
    Apply _ _ -> do
      let (headExpr, args) = spine expr []
      case headExpr of
        Local x -> do
          argTxts <- mapM (go 2) args
          renderUse req x argTxts
        _ -> do
          headTxt <- renderHead headExpr
          argTxts <- mapM (go 2) args
          Right (at req 1 (unwords (headTxt : argTxts)))
    Lambda [] body -> go req body
    Lambda pats body -> do
      binders <- mapM (renderPattern True) pats
      bodyTxt <- go 0 body
      Right (at req 0 ("fun " ++ unwords binders ++ " => " ++ bodyTxt))
    Tuple es -> do
      txts <- mapM (go 0) es
      Right (at req 2 ("\10216" ++ intercalate ", " txts ++ "\10217"))
    Let pat rhs body -> do
      patTxt <- renderPattern True pat
      rhsTxt <- go 0 rhs
      bodyTxt <- go 0 body
      Right (at req 0
        ("let " ++ patTxt ++ " := " ++ rhsTxt ++ "; " ++ bodyTxt))
    Case scrut [] -> do
      scrutTxt <- go 2 scrut
      Right (at req 0 ("nomatch " ++ scrutTxt))
    Case scrut alts -> do
      scrutTxt <- go 1 scrut
      altTxts <- mapM renderAlt alts
      Right (at req 0 ("match " ++ scrutTxt ++ " with " ++ unwords altTxts))
    Hole _ -> Left "candidate contains an unfilled hole"

  -- one use of a (possibly tagged) local with already-rendered term
  -- arguments: weave mid-spine placeholders, and instantiate the
  -- trailing quantifiers when the site is tagged
  renderUse req x argTxts =
    let name = stripTag x
        instantiate = tagged x
        -- a binder the goal fragment does not describe (bound inside an
        -- argument, say) simply takes its arguments as written
        woven = case Map.lookup name doms of
          Nothing -> argTxts
          Just frag -> weaveArgs frag argTxts
        trailing = case Map.lookup name doms of
          Just frag | instantiate -> trailingAlls frag (length argTxts)
          _ -> 0
        parts = name : woven ++ replicate trailing "_"
    in case parts of
      [only] -> Right (at req 2 only)
      _ -> Right (at req 1 (unwords parts))

  weaveArgs _ [] = []
  weaveArgs (FAll True _ rest) as = "_" : weaveArgs rest as
  weaveArgs (FAll False _ rest) as = weaveArgs rest as
  weaveArgs (FArr _ rest) (a : as) = a : weaveArgs rest as
  weaveArgs _ as = as

  at req level text = if level >= req then text else "(" ++ text ++ ")"

  spine (Apply f a) args = spine f (a : args)
  spine f args = (f, args)

  renderHead (Global name) = do
    kind <- globalKind name
    case kind of
      GInl -> Right ".inl"
      GInr -> Right ".inr"
      GUnit -> Right "\10216\10217"
  renderHead other = go 1 other

  -- non-final match-alternative bodies must not swallow following
  -- alternatives, so open bodies are parenthesized uniformly
  renderAlt (pat, body) = do
    patTxt <- renderPattern False pat
    bodyTxt <- go 1 body
    Right ("| " ++ patTxt ++ " => " ++ bodyTxt)

-- | @binder@ selects the irrefutable subset used after @fun@\/@let@;
-- match alternatives additionally allow constructor patterns.  The
-- top-level pattern needs no parentheses; nested constructor patterns do.
renderPattern :: Bool -> Pattern String -> Either String String
renderPattern = go False
 where
  go _ _ Wildcard = Right "_"
  go _ _ (Bind x) = Right x
  go _ binder (TuplePattern ps) = do
    txts <- mapM (go True binder) ps
    Right ("\10216" ++ intercalate ", " txts ++ "\10217")
  go atomic binder (Constructor c ps)
    | binder = Left "internal: constructor pattern survived normalization"
    | otherwise = do
        kind <- globalKind c
        case (kind, ps) of
          (GUnit, []) -> Right "_"
          (GInl, [p]) -> wrapped atomic ".inl" p
          (GInr, [p]) -> wrapped atomic ".inr" p
          _ -> Left "unexpected constructor pattern shape"
   where
    wrapped needParens ctor p = do
      sub <- go False binder p
      let text = ctor ++ " " ++ sub
      Right (if needParens then "(" ++ text ++ ")" else text)
  go _ _ (As _ _) = Left "internal: as-pattern survived normalization"
