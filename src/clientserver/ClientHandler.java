package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Arrays;

/**
 * ClientHandler.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class ClientHandler extends Thread {

	private Server server;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private String clientName;
	private String[] features;
	//TODO: bijhouden in bord?
	private String opponentName;
	private boolean loop;

	/**
	 * Constructs a ClientHandler object Initialises both Data streams. @
	 * requires server != null && sock != null;
	 */
	public ClientHandler(Server serverArg, Socket sockArg) throws IOException {
		this.server = serverArg;
		this.sock = sockArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
	}

	/**
	 * This method takes care of sending messages from the Client. Every message
	 * that is received, is preprended with the name of the Client, and the new
	 * message is offered to the Server for broadcasting. If an IOException is
	 * thrown while reading the message, the method concludes that the socket
	 * connection is broken and shutdown() will be called.
	 */
	public void run() {
		while (loop) {
			try {
				String line = in.readLine();
				String[] command = line.split("\\s+");
				//TODO: checken of command lengte etc klopt
				switch (command[0]) {
				case Client.CONNECT:
					clientName = command[1];
					features = Arrays.copyOfRange(command, 2,
							command.length - 1);
					//TODO: voeg client toe aan server (lobby)
					//TODO: broadcast de nieuwe lobby aan iedereen zonder game
					sendMessage(Server.ACCEPT_CONNECT
							+ " Feature array gescheiden met spaties");
					break;
				case Client.QUIT:
					//TODO: reason broadcasten?
					//TODO: broadcast de lobby als de client geen game had aan iedereen zonder game inclusief=
					shutdown();
					break;
				case Client.INVITE:
					String parameters = command[1];
					//Hopen dat die i ook checkt aan begin en niet eind elke loop
					for (int i = 2; i < command.length; i++) {
						parameters += " " + command[i];
					}
					server.sendMessage(command[1], Server.INVITE + " "
							+ parameters);
					break;
				case Client.ACCEPT_INVITE:
					//TODO: extras verzenden (spectators?)
					sendMessage(Server.GAME_START + " " + clientName + " "
							+ command[1]);
					server.sendMessage(command[1], Server.GAME_START + " "
							+ clientName + " " + command[1]);
					break;
				case Client.DECLINE_INVITE:
					server.sendMessage(command[1], Server.ERROR
							+ " Invite declined");
					break;
				case Client.MOVE:
					//TODO: zelf bord bijhouden voor nummer en move ok checken
					sendMessage(Server.MOVE_OK + " " + clientName + " "
							+ command[1]);
					server.sendMessage(opponentName, (Server.MOVE_OK + " "
							+ clientName + " " + command[1]));
					break;
				case Client.CHAT:
					String message = command[1];
					//Hopen dat die i ook checkt aan begin en niet eind elke loop
					for (int i = 2; i < command.length; i++) {
						message += " " + command[i];
					}
					server.broadcast(Server.CHAT + " " + message);
					break;
				case Client.REQUEST_BOARD:
					//TODO: zelf bord bijhouden om op te sturen
					break;
				case Client.REQUEST_LOBBY:
					//TODO: lobby maken
					break;
				case Client.REQUEST_LEADERBOARD:
					//TODO: leaderbords opslaan
					break;
				}
			} catch (IOException e) {
				shutdown();
			}
		}
	}

	/**
	 * This method can be used to send a message over the socket connection to
	 * the Client. If the writing of a message fails, the method concludes that
	 * the socket connection has been lost and shutdown() is called.
	 */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException ex) {
			shutdown();
		}
	}

	/**
	 * returns the name of the client
	 * 
	 * @return the name of the client
	 */
	public String getClientName() {
		return clientName;
	}

	/**
	 * returns the features of the client
	 * 
	 * @return the features of the client
	 */
	public String[] getClientFeatures() {
		return features;
	}

	/**
	 * This ClientHandler signs off from the Server and subsequently sends a
	 * last broadcast to the Server to inform that the Client is no longer
	 * participating in the chat.
	 */
	private void shutdown() {
		//TODO: verwijder speler (lobby)
		server.removeHandler(this);
		loop = false;
	}

} // end of class ClientHandler
