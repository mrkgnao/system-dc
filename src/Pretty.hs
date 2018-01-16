{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Pretty where

import           Types

import           Control.Applicative
import           Control.Lens
import           Data.Foldable
import           Data.Semigroup

import           Data.Text.Prettyprint.Doc                 (Doc, backslash, dot,
                                                            pipe, pretty)
import qualified Data.Text.Prettyprint.Doc                 as P
import           Data.Text.Prettyprint.Doc.Render.Terminal
import           Data.Text.Prettyprint.Doc.Util            (putDocW)

import qualified Data.Text.Lazy                            as TL
import qualified Data.Text.Lazy.IO                         as TL

import           Control.Monad.Reader
import           Data.String

type Out = Doc AnsiStyle

type OutM = PprM Out

type OutEndo = OutM -> OutM

type OutFold
   = forall f. Foldable f =>
                 f OutM -> OutM

renderStdout :: Pretty a => a -> IO ()
renderStdout = renderStdout' id

renderStdout' :: Pretty a => (OutM -> OutM) -> a -> IO ()
renderStdout' f = TL.putStrLn . renderText' f

renderText'' :: Pretty a => Bool -> (OutM -> OutM) -> a -> TL.Text
renderText'' c f =
  TL.replace "\\e" "\ESC" .
  renderLazy .
  P.layoutPretty layoutOpts .
  runPprM .
  (if c
     then id
     else fmap P.unAnnotate) .
  f . ppr
  where
    layoutOpts = P.LayoutOptions (P.AvailablePerLine 110 1.0)

renderText' :: Pretty a => (OutM -> OutM) -> a -> TL.Text
renderText' = renderText'' True

renderText :: Pretty a => a -> TL.Text
renderText = renderText' id

renderString :: Pretty a => a -> String
renderString = TL.unpack . renderText

renderPlainString :: Pretty a => a -> String
renderPlainString = TL.unpack . renderText'' False id

liftOutM :: (Foldable t) => ([a] -> b) -> t (PprM a) -> PprM b
liftOutM f = fmap f . sequence . toList

listed :: OutFold
listed = liftOutM P.list

sep, vsep, hsep, fsep :: OutFold
sep = liftOutM P.sep
vsep = liftOutM P.vsep
hsep = liftOutM P.hsep
fsep = liftOutM P.fillSep

cat, vcat, hcat, fcat :: OutFold
cat = liftOutM P.cat
vcat = liftOutM P.vcat
hcat = liftOutM P.hcat
fcat = liftOutM P.fillCat

group :: OutEndo
group = fmap P.group

annotate :: AnsiStyle -> OutEndo
annotate = fmap . P.annotate

unAnnotate :: OutEndo
unAnnotate = fmap P.unAnnotate

parens, angles, braces, brackets :: OutEndo
parens = fmap P.parens
angles = fmap P.angles
brackets = fmap P.brackets
braces = fmap P.braces

align :: OutEndo
align = fmap P.align

fill :: Int -> OutEndo
fill = fmap . P.fill

indent :: Int -> OutEndo
indent = fmap . P.indent

nest :: Int -> OutEndo
nest = fmap . P.nest

hang :: Int -> OutEndo
hang = fmap . P.hang

column :: (Int -> PprM Out) -> PprM Out
column f = PprM (\env -> P.column (pprWithEnv env . f))

nesting :: (Int -> PprM Out) -> PprM Out
nesting f = PprM (\env -> P.nesting (pprWithEnv env . f))

punctuate :: Out -> [Out] -> [OutM]
punctuate o = fmap pure . P.punctuate o

-- punctuate :: OutM -> PprM [Out] -> PprM [Out]
-- punctuate p os = P.punctuate <$> p <*> os
infixr 5 <+>

(<+>) :: OutM -> OutM -> OutM
(<+>) = liftA2 (P.<+>)

globalIndentWidth :: Int
globalIndentWidth = 4

newtype PprEnv = PprEnv
  { _pprEnv_precedence :: Int
  }

precedence :: Lens' PprEnv Int
precedence = lens _pprEnv_precedence (\e prec -> e {_pprEnv_precedence = prec})

newtype PprM a = PprM
  { unPprM :: PprEnv -> a
  } deriving (Functor, Applicative, Monad, MonadReader PprEnv, Semigroup)

pprWithEnv :: PprEnv -> PprM a -> a
pprWithEnv = flip unPprM

runPprM :: PprM a -> a
runPprM f = unPprM f iEnv
  where
    iEnv = PprEnv (-1)

assoc :: Int -> PprM a -> PprM a
assoc p = local (precedence .~ p)

infixr 8 %%

(%%) = assoc

pprPure :: Pretty a => a -> Out
pprPure = runPprM . ppr

class Pretty a where
  ppr :: a -> OutM

wrapOn :: Bool -> (PprM a -> PprM a) -> PprM a -> PprM a
wrapOn c f =
  if c
    then f
    else id

{-# INLINE wrapOn #-}
above :: Int -> (PprM a -> PprM a) -> PprM a -> PprM a
above p f m = do
  outerPrec <- view precedence
  wrapOn (outerPrec > p) f (assoc (p + 1) m)

infixr 8 ^^

prec ^^ body = above prec parens body

nowrap :: PprM a -> PprM a
nowrap = assoc (-1)
