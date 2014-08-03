## HW

HW is a language for hardware simulation. It is still under development.

### Example

	foo = 1 |> (\a -> (3 + a))

	main = let i = liftS2 (\s1 s2 -> s1 + s2 + foo)
	           <| (foldS (\acc a -> acc + 1) 1 clk)
	           <| (liftS (\a -> 1) clk)
	        in i