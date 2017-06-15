" Vim syntax file
" Language:     HEH
" Filenames:    *.heh
" Maintainers:  Artem Shinkarov <artyom.shinkaroff@gmail.com>
" URL:          https://raw.githubusercontent.com/ashinkarov/heh/master/vim/heh.vim
" Last Change:  2017-05-24

" quit when a syntax file was already loaded
if exists("b:current_syntax")
  finish
endif

" HEH is case sensitive.
syn case match

" lowercase identifier - the standard way to match
syn match    hehLCIdentifier /\<\(_\|\w\)*\>/

" Errors
syn match    hehBrackErr   "\]"
syn match    hehParenErr   ")"
syn match    hehThenErr    "\<then\>"

" Some convenient clusters
syn cluster  hehAllErrs contains=hehBrackErr,hehParenErr,hehThenErr

syn cluster  hehAENoParen contains=hehBrackErr,hehThenErr

syn cluster  hehContained contains=hehTodo


" Enclosing delimiters
syn region   hehEncl transparent matchgroup=hehNone start="(" matchgroup=hehNone end=")" contains=ALLBUT,@hehContained,hehParenErr
syn region   hehEncl transparent matchgroup=hehNone start="\[" matchgroup=hehNone end="\]" contains=ALLBUT,@hehContained,hehBrackErr


" Comments
syn region   hehComment start=";" end="$" contains=hehTodo,@Spell
syn keyword  hehTodo contained TODO FIXME XXX NOTE


" letrec
syn region   hehEnd matchgroup=hehKeyword start="\<letrec\>" matchgroup=hehKeyword end="\<in\>" contains=ALLBUT,@hehContained

" if
syn region   hehNone matchgroup=hehConditional start="\<if\>" matchgroup=hehConditional end="\<then\>" contains=ALLBUT,@hehContained,hehThenErr

syn region   hehEnd matchgroup=hehKeyword start="\<imap\>" matchgroup=hehKeyword end="{" contains=ALLBUT,@hehContained,hehThenErr


syn keyword  hehConditional  else
syn keyword  hehKeyword  reduce filter
syn match    hehKeyword  "\\"
syn match    hehKeyword  "λ"
syn match    hehKeyword  "_"

syn keyword  hehBoolean      true false

syn match    hehNumber	      "\<\d\+\>"
syn match    hehNumber	      "\<omega\>"
syn match    hehNumber	      "\<ω\>"

" Synchronization
syn sync minlines=20
syn sync maxlines=500


" Define the default highlighting.
" Only when an item doesn't have highlighting yet

hi def link hehBrackErr     Error
hi def link hehParenErr     Error
hi def link hehCommentErr   Error
hi def link hehThenErr      Error

hi def link hehComment      Comment

hi def link hehKeyword      Keyword

hi def link hehBoolean      Boolean

hi def link hehConditional  Conditional

hi def link hehNumber       Number

hi def link hehTodo         Todo

hi def link hehEncl         Keyword


let b:current_syntax = "heh"

" vim: ts=8
