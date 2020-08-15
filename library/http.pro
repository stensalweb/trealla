:- module(http, [http_open/3, http_get/3, http_post/4, http_put/4, http_delete/3]).

http_response(S,Code) :-
	getline(S,Line),
	split(Line,' ',[_Ver,Rest]),
	split(Rest,' ',[Code2,_Rest2]),
	atom_number(Code2,Code).

http_headers(S,Pair) :-
	repeat,
		(at_end_of_stream(S) -> (!, fail) ; true),
		getline(S,Line),
		split(Line,':',[K,V]),
		(K == '' -> (!, fail) ; true),
		string_lower(K,K2),
		string_lower(V,V2),
		Pair=K2:V2.

http_chunked(S,Tmp,Data) :-
	getline(S,Line),
	atom_hex(Line,Len),
	Len > 0,
	bread(S,Len,Tmp2),
	getline(S,_),
	atom_concat(Tmp,Tmp2,Tmp3),
	http_chunked(S,Tmp3,Data).
http_chunked(_,Data,Data).

http_read(S,Hdrs,Data) :-
	dict:get(Hdrs,'content-length',V,_),
	(atom(V) -> atom_number(V,Len) ; Len=V),
	bread(S,Len,Data).

http_open([],_,_) :- !, fail.

http_open(UrlList,S,Opts) :-
	is_list(UrlList),
	is_list(Opts),
	union(UrlList,Opts,OptList),
	memberchk(host(Host),UrlList),
	memberchk(path(Path),UrlList),
	(memberchk(method(Method),OptList) -> true ; Method = get),
	(memberchk(version(Maj-Min),OptList) -> true ; (Maj = 1, Min = 1)),
	client(Host,_Host,_Path,S,OptList),
	string_upper(Method,UMethod),
	format(S,'~a /~a HTTP/~d.~d\r~nHost: ~a\r~nConnection: keep-alive\r~n\r~n', [UMethod,Path,Maj,Min,Host]),
	http_response(S,Code),
	findall(Hdr,http_headers(S,Hdr),Hdrs),
	atom_concat(Host,Path,Url),
	dict:get(Hdrs,'location',Location,Url),
	ignore(memberchk(status_code(Code),OptList)),
	ignore(memberchk(headers(Hdrs),OptList)),
	ignore(memberchk(final_url(Location),OptList)),
	true.

http_process(Url,S,Opts) :-
	atom(Url),
	is_list(Opts),
	OptList=Opts,
	(memberchk(post(PostData),OptList) -> Method2 = post ; Method2 = get),
	(memberchk(method(Method),OptList) -> true ; Method = Method2),
	(memberchk(version(Maj-Min),OptList) -> true ; (Maj = 1, Min = 1)),
	client(Url,Host,Path,S,OptList),
	string_upper(Method,UMethod),
	(memberchk(header('content_type',Ct),OptList) ->
		format(atom(Ctype),'Content-Type: ~w\r~n',[Ct]) ; Ctype = '' ),
	(nonvar(PostData) ->
		(atom_length(PostData,DataLen), format(atom(Clen),'Content-Length: ~d\r~n',[DataLen])) ; Clen = '' ),
	format(S,'~a /~a HTTP/~d.~d\r~nHost: ~a\r~nConnection: close\r~n~w~w\r~n', [UMethod,Path,Maj,Min,Host,Ctype,Clen]),
	(nonvar(DataLen) -> bwrite(S,PostData) ; true),
	http_response(S,Code),
	findall(Hdr,http_headers(S,Hdr),Hdrs),
	ignore(memberchk(status_code2(Code),OptList)),
	ignore(memberchk(headers2(Hdrs),OptList)),
	true.

http_get(Url,Data,Opts) :-
	Opts2=[headers2(Hdrs2)|Opts],
	Opts3=[status_code2(Code2)|Opts2],
	http_process(Url,S,Opts3),
	dict:get(Hdrs2,'transfer-encoding',V,''),
	(V == chunked -> http_chunked(S,'',Data2) ; http_read(S,Hdrs2,Data2)),
	close(S),
	((Code2 >= 301, Code2 =< 302) ->
		(dict:get(Hdrs2,'location',Url2,''),
		ignore(memberchk(final_url(Url2),Opts)),
		http_get(Url2,Data,Opts))
	;
		(Data=Data2,
		ignore(memberchk(final_url(Url),Opts)),
		ignore(memberchk(status_code2(V1),Opts3)),
		ignore(memberchk(status_code(V1),Opts)),
		ignore(memberchk(headers2(V2),Opts3)),
		ignore(memberchk(headers(V2),Opts)))
	),
	true.

http_post(Url,Data,Reply,Opts) :-
	http_get(Url,Reply,[post(Data)|Opts]).

http_put(Url,Data,Reply,Opts) :-
	http_post(Url,Data,Reply,[method(put)|Opts]).

http_delete(Url,Data,Opts) :-
	http_get(Url,Data,[method(delete)|Opts]).
