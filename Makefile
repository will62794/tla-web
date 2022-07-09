serve:
	python -m SimpleHTTPServer 8080

test:
	cd specs/with_state_graphs && bash gen_state_graphs.sh