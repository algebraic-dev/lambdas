module Util where

colorize :: String -> String -> String
colorize s e = s ++ e ++ "\x1b[0m"

bright :: String -> String
bright = colorize "\x1b[1m"

dim :: String -> String
dim = colorize "\x1b[2m"

red :: String -> String
red = colorize "\x1b[31m"

green :: String -> String
green = colorize "\x1b[32m"

blue :: String -> String
blue = colorize "\x1b[34m"

yellow :: String -> String
yellow = colorize "\x1b[33m"
