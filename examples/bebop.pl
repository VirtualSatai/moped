# Creates the example from the Bebop paper with a given number of procedures.

my $n = $ARGV[0];
my $i;

print <<EOF;
decl g;
void main()
begin
  level1();
  level1();
  if (!g) then
    reach: skip;
  else
    skip;
  fi
end

EOF

for ($i = 1; $i <= $n; $i++) {
  printf "void level%d()\n",$i;
  print <<EOF;
begin
  decl a,b,c;
  if(g) then
    a,b,c := 0,0,0;
    while(!a|!b|!c) do
      if (!a) then
        a := 1;
      elsif (!b) then
        a,b := 0,1;
      elsif (!c) then
        a,b,c := 0,0,1;
      fi
    od
  else
EOF
  if ($i == $n) {
	printf "    skip; skip;\n";
  } else {
	printf "    level%d(); level%d();\n",$i+1,$i+1;
  }
  print <<EOF;
  fi
  g := !g;
end

EOF
}
