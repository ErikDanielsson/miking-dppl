import pyqtgraph as pg
import numpy as np
from pyqtgraph.Qt import QtCore, QtGui, QtWidgets
import sys
import json
import re
from collections import Counter
import time
from pathlib import Path
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
import random


# Qt Signal for thread-safe updates
class PlotUpdateSignal(QtCore.QObject):
    update_requested = QtCore.pyqtSignal()


def flatten_incremental(flat_samples, new_samples):
    """Incrementally add new samples to flattened data."""
    if not new_samples:
        return flat_samples

    # Initialize if needed
    if not flat_samples:
        flat_samples = dict([(k, []) for k in new_samples[0].keys()])
        flat_samples.update({f"lambda{i}": [] for i in range(4)})

    # Add new samples
    for s in new_samples:
        for k, v in s.items():
            if k != "lambda":
                flat_samples[k].append(v)
            else:
                for i, lv in enumerate(v):
                    if f"lambda{i}" not in flat_samples:
                        flat_samples[f"lambda{i}"] = []
                    flat_samples[f"lambda{i}"].append(lv)

    return flat_samples


def load_new_samples(file_pos=0):
    """Load only new samples from current file position.

    Returns: (new_samples, new_accumulated_flat_samples, new_file_pos)
    """
    try:
        new_samples = []
        with open("hrm-samples.json") as fh:
            # Skip to where we left off
            fh.seek(file_pos)
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    parts = line.split("\t", 1)
                    if len(parts) != 2:
                        continue
                    sample_num_str, json_str = parts
                    data = json.loads(json_str)
                    new_samples.append(data)
                except (json.JSONDecodeError, ValueError):
                    continue
            new_pos = fh.tell()
        return new_samples, new_pos
    except FileNotFoundError:
        return [], file_pos


def clear_axes(fig):
    """Clear all axes in a figure."""
    for ax in fig.get_axes():
        ax.clear()


def update_plots(plots, samples, subsample_threshold=50000):
    """Update all plots with new data using PyQtGraph."""
    plot_vars = ["mu", "beta", "lambda0", "lambda1", "lambda2", "lambda3"]

    for i, var in enumerate(plot_vars):
        hist_plot = plots[f"{var}_hist"]
        trace_plot = plots[f"{var}_trace"]

        # Clear previous data
        hist_plot.clear()
        trace_plot.clear()

        if samples and var in samples and samples[var]:
            try:
                data = np.array(samples[var], dtype=float)

                # Histogram
                if len(data) > subsample_threshold:
                    hist_data = np.random.choice(
                        data, subsample_threshold, replace=False
                    )
                else:
                    hist_data = data

                # PyQtGraph proper histogram with bars
                hist, bin_edges = np.histogram(hist_data, bins=30)
                bin_centers = (bin_edges[:-1] + bin_edges[1:]) / 2
                bin_width = bin_edges[1] - bin_edges[0]

                # Create bar graph item
                bar_graph = pg.BarGraphItem(
                    x=bin_centers,
                    height=hist,
                    width=bin_width * 0.8,
                    brush=pg.mkBrush(100, 149, 237, 200),
                    pen=pg.mkPen(color=(50, 100, 200), width=1),
                )
                hist_plot.addItem(bar_graph)

                # Trace plot
                trace_plot.plot(data, pen=pg.mkPen(color=(100, 149, 237), width=0.5))

                print(f"Plotted {var}: {len(data)} samples")

            except Exception as e:
                print(f"Error plotting {var}: {e}")
                import traceback

                traceback.print_exc()

        # Set titles and limits
        hist_plot.setTitle(f"{var} (Histogram, n={len(samples.get(var, []))})")
        trace_plot.setTitle(f"{var} (Trace)")

        if var.startswith("lambda"):
            hist_plot.setXRange(0, 1)
            trace_plot.setYRange(0, 1)


def print_statistics(samples):
    """Print statistics about the samples."""
    if not samples:
        return

    print("\n" + "=" * 60)
    print(f"Updated at {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)
    for k, v in samples.items():
        print(k)
        if re.match(r"^\d", k):
            # Convert sublists to tuples for hashing if needed
            if v and isinstance(v[0], list):
                hashable_v = [tuple(item) for item in v]
            else:
                hashable_v = v
            d = len(hashable_v[0])
            uniq = set(hashable_v)
            print(f"{k}: {len(uniq)} (/{3**d - 2**d})")
            print(uniq)


class SampleFileHandler(FileSystemEventHandler):
    """Handler for file change events."""

    def __init__(self, signal, plots):
        self.signal = signal
        self.plots = plots
        self.last_update = 0
        self.file_pos = 0
        self.accumulated_samples = {}

    def on_modified(self, event):
        """Called when the monitored file is modified."""
        if event.src_path.endswith("hrm-samples.json"):
            # Debounce: only update if 5+ seconds have passed
            current_time = time.time()
            if current_time - self.last_update > 5.0:
                self.last_update = current_time
                try:
                    new_samples, self.file_pos = load_new_samples(self.file_pos)
                    if new_samples:
                        self.accumulated_samples = flatten_incremental(
                            self.accumulated_samples, new_samples
                        )
                        # Store samples for main thread to access
                        self.plots["_accumulated_samples"] = self.accumulated_samples
                        # Emit signal to trigger update in main thread
                        self.signal.update_requested.emit()
                        print_statistics(self.accumulated_samples)
                except Exception as e:
                    print(f"Error updating samples: {e}")


def main():
    """Main function - set up plots and file watcher."""
    # Create Qt application
    app = QtWidgets.QApplication(sys.argv)

    # Create signal for thread-safe updates
    update_signal = PlotUpdateSignal()

    # Create main window
    win = QtWidgets.QMainWindow()
    win.setWindowTitle("Sample Plots - Real-time Monitor")
    win.resize(1000, 1600)

    # Create central widget and layout
    central = QtWidgets.QWidget()
    win.setCentralWidget(central)
    layout = QtWidgets.QGridLayout()
    central.setLayout(layout)

    # Create plots dictionary
    plots = {}
    plot_vars = ["mu", "beta", "lambda0", "lambda1", "lambda2", "lambda3"]

    # Set pyqtgraph background and foreground
    pg.setConfigOption("background", "w")
    pg.setConfigOption("foreground", "k")

    for i, var in enumerate(plot_vars):
        # Histogram plot (left column)
        hist_plot = pg.PlotWidget(title=f"{var} (Histogram)")
        hist_plot.setLabel("left", "Count")
        hist_plot.setLabel("bottom", var)
        layout.addWidget(hist_plot, i, 0)
        plots[f"{var}_hist"] = hist_plot

        # Trace plot (right column)
        trace_plot = pg.PlotWidget(title=f"{var} (Trace)")
        trace_plot.setLabel("left", var)
        trace_plot.setLabel("bottom", "Iteration")
        layout.addWidget(trace_plot, i, 1)
        plots[f"{var}_trace"] = trace_plot

    # Show window
    win.show()

    # Initial load - get all samples and current file position
    print("Loading initial samples...")
    initial_samples, file_pos = load_new_samples(0)
    accumulated_samples = flatten_incremental({}, initial_samples)

    print(f"Initial samples loaded: {len(accumulated_samples)} variables")
    if accumulated_samples:
        print(
            f"Sample counts: {[(k, len(v)) for k, v in list(accumulated_samples.items())[:6]]}"
        )

    # Update with initial data
    print("Updating plots with initial data...")
    update_plots(plots, accumulated_samples)
    print_statistics(accumulated_samples)

    # Create file handler with signal
    event_handler = SampleFileHandler(update_signal, plots)
    event_handler.file_pos = file_pos
    event_handler.accumulated_samples = accumulated_samples

    # Connect signal to update function
    def on_update_requested():
        if "_accumulated_samples" in plots:
            update_plots(plots, plots["_accumulated_samples"])

    update_signal.update_requested.connect(on_update_requested)

    # Start file observer
    observer = Observer()
    observer.schedule(event_handler, path=".", recursive=False)
    observer.start()

    print("\nWatching hrm-samples.json for changes...")
    print("Press Ctrl+C or close window to exit.\n")

    # Run Qt event loop
    try:
        sys.exit(app.exec_())
    except KeyboardInterrupt:
        print("\nShutting down...")
        observer.stop()
        observer.join()


if __name__ == "__main__":
    main()
