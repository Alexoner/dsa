-- union of tables
select distinct(name) from (
	select distinct(name) from t1
	union
	select distinct(name) from t2
	union
	select distinct(name) from t3
) a
where name is not NULL

