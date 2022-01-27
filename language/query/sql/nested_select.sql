--  SELECT query can be nested using subquery of select
--  Input: Activities=UserId,[Date],Activity... Users=UserId,Profile...,[Date]
--  Output: Activies joined with latest User profile, (Users keeps all the history)
--  a simple select query:
select *
from A
where 1=1
;

--  a nested select query
select *
from (
	select * from Activities
) B
where 1=1
;

select
*
from
Activities inner join
(
	select -- Latest User record: argmax(Date) group by UserId
	Users.*
	from
	Users
	join (
		select UserId, max([Date]) as MaxDate
		from Users
		group by UserId
	) B
	on Users.UserId=B.UserId and Users.[Date] = B.MaxDate
) C
on Activities.Id=C.Id

