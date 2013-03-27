#!/bin/sh
sed '/^::\$EOF/ q' | sed -r '/^ *::|^ *$/ d'
