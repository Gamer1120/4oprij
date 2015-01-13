import java.util.Observer;

public interface GameView extends Observer {
	public void start();

	public void reset();

	public void play();

	public void update();

	public void printResult();
}
