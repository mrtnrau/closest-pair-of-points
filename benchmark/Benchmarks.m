clear
clc
close all

%% Experimental Data
n = [ 10000,  20000,  30000,  40000,  50000,  60000,  70000,  80000,  90000,...
     100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 900000];
%s = [     21,     43,    72,      98,    121,    160,    175,    203,   237,...
%         266,    681,  1115,    1472,   1892,   2498,   2859,   3426,  3861];
j = [     20,     44,    71,      96,    116,    159,    176,    197,   236,...
         263,    663,  1047,    1419,   1896,   2540,   2822,   3430,  3888];
c = [     45,     99,   158,     226,    281,    348,    419,    472,   557,...
         624,   1472,  2561,    3297,   4391,   5522,   6427,   7489,  8559];
o = [     20,     46,    73,     107,    129,    166,    210,    242,   262,...
	 293,    689,  1222,    1598,   2181,   2883,   3170,   3635,  4259];
i = [     29,     65,   107,     157,    209,    264,    340,    411,   467,...
         590,   1418,  2427,    3383,   4527,   5689,   6716,   7935,  9136];

mean(i./o)
mean(i./j)
mean(o./j)
mean(c./o)

%% Non-linear regression
model = @(beta,x)(beta(1) + beta(2).*x + beta(3).*x.*log2(x));

%s_var0 = [1.0, 1.0, 1.0];
%s_var = nlinfit(n, s, model, s_var0, 'ErrorModel', 'proportional');
%s_fitted = model(s_var, n);
%s_var

j_var0 = [1.0, 1.0, 1.0];
j_var = nlinfit(n, j, model, j_var0, 'ErrorModel', 'proportional');
j_fitted = model(j_var, n);
j_var

c_var0 = [1.0, 1.0, 1.0];
c_var = nlinfit(n, c, model, c_var0, 'ErrorModel', 'proportional');
c_fitted = model(c_var, n);
c_var

o_var0 = [1.0, 1.0, 1.0];
o_var = nlinfit(n, o, model, o_var0, 'ErrorModel', 'proportional');
o_fitted = model(o_var, n);
o_var

i_var0 = [1.0, 1.0, 1.0];
i_var = nlinfit(n, i, model, i_var0, 'ErrorModel', 'proportional');
i_fitted = model(i_var, n);
i_var

%% Constants
%red    = [197/255,  28/255,   8/255];
orange = [218/255, 124/255,  48/255];
blue   = [ 57/255, 106/255, 177/255];
green  = [ 62/255, 150/255,  81/255];
purple = [128/255,   0/255, 128/255];

marker_size = 50;
line_width = 1.5;

%% Figure
figure
hold on
grid on

%scatter(n, s, marker_size, red    , 'filled', '>')
scatter(n, j, marker_size, orange   , 'filled', 'd')
scatter(n, c, marker_size, green , 'filled', 'o')
scatter(n, o, marker_size, blue  , 'filled', 's')
scatter(n, i, marker_size, purple, 'filled', '^')

%plot(n, s_fitted, 'Color', red   , 'LineWidth', line_width)
plot(n, j_fitted, 'Color', orange, 'LineWidth', line_width)
plot(n, c_fitted, 'Color', green , 'LineWidth', line_width)
plot(n, o_fitted, 'Color', blue  , 'LineWidth', line_width)
plot(n, i_fitted, 'Color', purple, 'LineWidth', line_width)

set(gca, 'yScale', 'log')
set(gca, 'xScale', 'log')

xlabel('Number of Points' , 'FontWeight', 'bold')
ylabel('Running Time (ms)', 'FontWeight', 'bold')

legend('Basic-2', 'Basic-7', 'Ocaml', 'Isabelle', 'Location', 'best')
