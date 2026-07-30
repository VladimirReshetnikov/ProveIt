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
-- The engine is never trusted (design rule 2): a rendering failure just
-- drops the candidate, and everything shown has been verified.
module Leant.Synth.Render
  ( renderLeanTerm
  ) where

import Data.List (intercalate)
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

-- | Render one candidate expression as Lean text, or explain (internally)
-- why it cannot be rendered; the caller drops such candidates.
renderLeanTerm :: Expression String -> Either String String
renderLeanTerm expr0 = do
  let expr1 = normalizeExpr 0 expr0
  expr2 <- uniquify expr1
  render 0 expr2

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
-- source term stays correct).

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

-- Rendering ------------------------------------------------------------------
--
-- Precedence levels: 0 = open (fun/match/let/nomatch), 1 = application,
-- 2 = atom.  A subterm rendered in a position requiring a higher level is
-- parenthesized.

render :: Int -> Expression String -> Either String String
render req expr = case expr of
  Local x -> Right (at 2 x)
  Global name -> do
    kind <- globalKind name
    case kind of
      GUnit -> Right (at 2 "\10216\10217")
      GInl -> Right (at 0 ".inl")
      GInr -> Right (at 0 ".inr")
  Apply _ _ -> do
    let (headExpr, args) = spine expr []
    headTxt <- renderHead headExpr
    argTxts <- mapM (render 2) args
    Right (at 1 (unwords (headTxt : argTxts)))
  Lambda [] body -> render req body
  Lambda pats body -> do
    binders <- mapM (renderPattern True) pats
    bodyTxt <- render 0 body
    Right (at 0 ("fun " ++ unwords binders ++ " => " ++ bodyTxt))
  Tuple es -> do
    txts <- mapM (render 0) es
    Right (at 2 ("\10216" ++ intercalate ", " txts ++ "\10217"))
  Let pat rhs body -> do
    patTxt <- renderPattern True pat
    rhsTxt <- render 0 rhs
    bodyTxt <- render 0 body
    Right (at 0 ("let " ++ patTxt ++ " := " ++ rhsTxt ++ "; " ++ bodyTxt))
  Case scrut [] -> do
    scrutTxt <- render 2 scrut
    Right (at 0 ("nomatch " ++ scrutTxt))
  Case scrut alts -> do
    scrutTxt <- render 1 scrut
    altTxts <- mapM renderAlt alts
    Right (at 0 ("match " ++ scrutTxt ++ " with " ++ unwords altTxts))
  Hole _ -> Left "candidate contains an unfilled hole"
 where
  at level text = if level >= req then text else "(" ++ text ++ ")"

  spine (Apply f a) args = spine f (a : args)
  spine f args = (f, args)

  renderHead (Global name) = do
    kind <- globalKind name
    case kind of
      GInl -> Right ".inl"
      GInr -> Right ".inr"
      GUnit -> Right "\10216\10217"
  renderHead other = render 1 other

  -- non-final match-alternative bodies must not swallow following
  -- alternatives, so open bodies are parenthesized uniformly
  renderAlt (pat, body) = do
    patTxt <- renderPattern False pat
    bodyTxt <- render 1 body
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
