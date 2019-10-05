clear
clc
close all

%% Experimental Data
n = [ 10000,  20000,  30000,  40000,  50000,  60000,  70000,  80000,  90000,...
     100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 900000];
m = [    14,     30,     48,     94,     91,    116,    144,    164,    191,...
        313,    541,    898,   1479,   1678,   2141,   2706,   3074,   3533];
i = [    25,     63,    111,    163,    212,    269,    332,    385,    451,...
        530,   1263,   2099,   2977,   3922,   4874,   5860,   6870,   7937];
v = [   188,    428,    692,    966,   1237,   1546,   1883,   2167,   2508,...
       2819,   6198,   9976,  13657,  17760,  21862,  26108,  30286,  34830];

mean(v./m)
mean(v./i)

%% Non-linear regression
model = @(beta,x)(beta(1).*x.*log2(x));

m_var0 = 0.0002;
m_var = nlinfit(n, m, model, m_var0, 'ErrorModel', 'proportional');
m_var
m_fitted = model(m_var, n);

i_var0 = 0.0005;
i_var = nlinfit(n, i, model, i_var0, 'ErrorModel', 'proportional');
i_var
i_fitted = model(i_var, n);

v_var0 = 0.002;
v_var = nlinfit(n, v, model, v_var0, 'ErrorModel', 'proportional');
v_var
v_fitted = model(v_var, n);

%% Constants
blue = [57/255, 106/255, 177/255];
orange = [218/255, 124/255, 48/255];
green = [62/255, 150/255, 81/255];
marker_size = 40;
line_width = 1.5;

%% Figure
figure
hold on
grid on

scatter(n, m, marker_size, blue, 'filled', 'o')
scatter(n, i, marker_size, orange, 'filled', '^')
scatter(n, v, marker_size, green, 'filled', 's')

plot(n, m_fitted, 'Color', blue, 'LineWidth', line_width)
plot(n, i_fitted, 'Color', orange, 'LineWidth', line_width)
plot(n, v_fitted, 'Color', green, 'LineWidth', line_width)

set(gca, 'yScale', 'log')
set(gca, 'xScale', 'log')

xlabel('Number of Points', 'FontWeight', 'bold')
ylabel('Execution Time (ms)', 'FontWeight', 'bold')

legend('mutable', 'immutable', 'verified', 'Location', 'best')
