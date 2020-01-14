clear
clc
close all

%% Experimental Data
n = [ 10000,  20000,  30000,  40000,  50000,  60000,  70000,  80000,  90000,...
     100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 900000];
m = [     22,     45,     72,     94,    135,    148,    176,    201,    230,...
         286,    580,   1025,   1459,   1855,	2366,	2878,	3195,	3690];		
i = [     20,     44,     73,    101,    130,    167,    199,    231,    265,...
         305,	 714,	1170,	1593,	2111,	2615,	3062,	3579,	4103];		
v = [     28,     65,    109,    157,    206,    263,    336,    388,    460,...
         548,	1351,	2275,	3247,	4274,	5379,	6539,	7466,	8601];

mean(v./m)
mean(v./i)
mean(w./m)
mean(w./i)

%% Non-linear regression
model = @(beta,x)(beta(1) + beta(2).*x + beta(3).*x.*log2(x));

m_var0 = [1.0, 1.0, 1.0];
m_var = nlinfit(n, m, model, m_var0, 'ErrorModel', 'proportional');
m_fitted = model(m_var, n);

i_var0 = [1.0, 1.0, 1.0];
i_var = nlinfit(n, i, model, i_var0, 'ErrorModel', 'proportional');
i_fitted = model(i_var, n);

v_var0 = [1.0, 1.0, 1.0];
v_var = nlinfit(n, v, model, v_var0, 'ErrorModel', 'proportional');
v_fitted = model(v_var, n);

w_var0 = [1.0, 1.0, 1.0];
w_var = nlinfit(n, w, model, w_var0, 'ErrorModel', 'proportional');
w_fitted = model(w_var, n);

%% Constants
blue = [57/255, 106/255, 177/255];
orange = [218/255, 124/255, 48/255];
green = [62/255, 150/255, 81/255];
purple = [128/255, 0/255, 128/255];
marker_size = 40;
line_width = 1.5;

%% Figure
figure
hold on
grid on

scatter(n, m, marker_size, blue, 'filled', 'o')
scatter(n, i, marker_size, orange, 'filled', '^')
scatter(n, v, marker_size, green, 'filled', 's')
scatter(n, w, marker_size, purple, 'filled', 'd')

plot(n, m_fitted, 'Color', blue, 'LineWidth', line_width)
plot(n, i_fitted, 'Color', orange, 'LineWidth', line_width)
plot(n, v_fitted, 'Color', green, 'LineWidth', line_width)
plot(n, w_fitted, 'Color', purple, 'LineWidth', line_width)

set(gca, 'yScale', 'log')
set(gca, 'xScale', 'log')

xlabel('Number of Points', 'FontWeight', 'bold')
ylabel('Running Time (ms)', 'FontWeight', 'bold')

legend('imperative', 'functional', 'verified', 'verified alternative', 'Location', 'best')
