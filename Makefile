pdf:
	isabelle build -d . -v cap9-spec

html:
	isabelle build -d . -o browser_info -v cap9-spec

clean:
	rm -rf output
