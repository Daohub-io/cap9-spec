pdf:
	isabelle build -d . -d Word_Lib -v cap9-spec

html:
	isabelle build -d . -o browser_info -v cap9-spec

clean:
	rm -rf output
