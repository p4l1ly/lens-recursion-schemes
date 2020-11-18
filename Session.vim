let SessionLoad = 1
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
cd ~/hobby/lens-recursion-schemes
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +1 term://.//154180:/bin/zsh
badd +103 src/Control/RecursionSchemes/Lens.hs
badd +7 hie.yaml
badd +2 .gitignore
badd +179 test/Test.hs
argglobal
%argdel
edit test/Test.hs
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
2wincmd h
wincmd w
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=0
set winheight=1
set winminwidth=0
set winwidth=1
exe 'vert 1resize ' . ((&columns * 127 + 190) / 381)
exe 'vert 2resize ' . ((&columns * 82 + 190) / 381)
exe 'vert 3resize ' . ((&columns * 170 + 190) / 381)
argglobal
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 194 - ((65 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
194
normal! 035|
wincmd w
argglobal
if bufexists("src/Control/RecursionSchemes/Lens.hs") | buffer src/Control/RecursionSchemes/Lens.hs | else | edit src/Control/RecursionSchemes/Lens.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 150 - ((26 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
150
normal! 03|
wincmd w
argglobal
if bufexists("term://.//154180:/bin/zsh") | buffer term://.//154180:/bin/zsh | else | edit term://.//154180:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 73 - ((72 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
73
normal! 0
wincmd w
2wincmd w
exe 'vert 1resize ' . ((&columns * 127 + 190) / 381)
exe 'vert 2resize ' . ((&columns * 82 + 190) / 381)
exe 'vert 3resize ' . ((&columns * 170 + 190) / 381)
tabnext 1
if exists('s:wipebuf') && getbufvar(s:wipebuf, '&buftype') isnot# 'terminal'
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20 winminheight=1 winminwidth=1 shortmess=filnxtToOFc
let s:sx = expand("<sfile>:p:r")."x.vim"
if file_readable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &so = s:so_save | let &siso = s:siso_save
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
