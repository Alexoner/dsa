-- Calculate running total(cumulative sum)
--  Inut: Date | Sales|
--  Output: Date | Runnint total of Sales
--  Solution:
--  join on inequality condition
--  and aggregate with group by for the column
select
    a.date,
    sum(b.sales) as cumulative_sales
from sales_table a
join sales_table b on a.date >= b.date
group by a.date
order by a.date;
