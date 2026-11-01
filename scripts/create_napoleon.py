#!/usr/bin/env python3
"""Assemble the locally authored campaign; no API call and no invented benchmark."""
import json
import time
import argparse
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Each main stage has its own place, incident and spatial action.
STAGES = [
("Le camp des savants", "Napoléon Bonaparte attend devant une table couverte de cartes. Un relevé des puits du Nil a disparu ; sans lui, soldats et villages risquent de manquer d'eau.", "Parler à Napoléon Bonaparte"),
("La tente de Salma", "Salma attend sous une toile rayée. La cartographe reconnaît une marque sur l'étui abandonné : le voleur a quitté le camp par le port.", "Examiner la carte avec Salma"),
("Les quais d'Alexandrie", "Les amarres grincent au milieu des ballots. Un contrebandier tente d'écarter les curieux d'une caisse portant le sceau de l'expédition.", "Prendre le sentier le long des quais"),
("Le registre du magasinier", "Lucien Morel demande pourquoi un reçu mentionne deux fois le même bateau. Une tache d'encre masque le nom du destinataire.", "Examiner le registre"),
("La cour des entrepôts", "Une ombre referme une caisse derrière des jarres. Vous pouvez attendre le passage des porteurs ou défier le guetteur qui surveille la cour.", "Suivre les porteurs par le passage"),
("Le balcon du négociant", "Salma attend près d'une fenêtre ouverte. Elle a retrouvé le nom d'un passeur qui connaît les canaux mieux que les officiers.", "Passer par la fenêtre vers le canal"),
("Les cordages coupés", "Youssef attend près d'une barque détachée. Quelqu'un a saboté son embarcation ; un homme armé prétend désormais percevoir un droit de passage.", "Parler à Youssef pour trouver une autre barque"),
("La maison du pilote", "Le pilote dessine les bras du fleuve sur une dalle humide. La route de Rosette reste ouverte si vous passez avant le convoi des vivres.", "Examiner le dessin sur la dalle"),
("La digue des salines", "Le vent pousse le sel contre vos bottes. Un garde irrégulier barre le chemin direct, mais les ouvriers empruntent une passerelle latérale.", "Monter l'échelle de la passerelle"),
("La voile rapiécée", "Youssef attend à l'ombre d'une voile bleue. Il accepte de vous conduire jusqu'à la première écluse en échange d'un coup de main aux amarres.", "Monter dans la barque de Youssef"),
("Le poste abandonné", "Une lanterne brûle encore dans la guérite. Le guetteur revenu sur ses pas veut reprendre le carnet que vous avez aperçu.", "Parler au guetteur pour obtenir le passage"),
("La borne du canal", "Trois traits gravés indiquent une dérivation vers les terres cultivées. Salma reconnaît la méthode d'un ingénieur de l'expédition.", "Examiner les trois traits"),
("Les greniers de Rosette", "Des sacs de grain forment un dédale silencieux. Un maraudeur protège une cache ; des habitants vous montrent une sortie vers le marché.", "Suivre le sentier indiqué vers le marché"),
("Le marché aux cordes", "Amina demande des nouvelles du convoi. Elle a vu passer un homme tenant l'étui des cartes comme s'il contenait un trésor.", "Parler à Amina"),
("L'atelier du relieur", "Le relieur a réparé la couture d'un carnet couvert de sable. Une page arrachée porte un dessin de barrage et les initiales d'un officier.", "Ouvrir le coffre des papiers"),
("La première halte sur le Nil", "Le fleuve devient orange au coucher du soleil. Youssef vous avertit que la prochaine étape exige de choisir entre la rive et les canaux.", "Rejoindre la barque au bord du Nil"),
("Les roseaux du delta", "Une étroite trouée serpente entre les roseaux. Le bruit d'une rame vous permet de suivre une embarcation sans l'approcher.", "Suivre le sentier des roseaux"),
("Le moulin à eau", "Une roue immobile retient les débris d'une crue. Une pièce du mécanisme ressemble au croquis du carnet volé.", "Monter l'escalier du moulin"),
("La cour des potiers", "Amina attend près d'un four refroidi. Les potiers ont transporté des jarres pour des hommes qui parlaient d'une citerne secrète.", "Parler à Amina près du four"),
("La terrasse des palmiers", "Salma observe les ombres des palmiers. Elle en déduit que le dessin du carnet a été tracé dans une cour orientée vers l'est.", "Observer la rive avec la longue-vue"),
("Le ponton du convoi", "Un déserteur garde un coffre de documents militaires. Le responsable des vivres connaît toutefois un chemin qui évite son poste.", "Suivre le chemin du convoi"),
("Les tentes de l'infirmerie", "Le médecin vous demande d'épargner les réserves d'eau. Un blessé a entendu le nom d'un village où les cartes doivent être échangées.", "Parler au médecin de l'infirmerie"),
("La lettre de Desaix", "Le général Desaix attend devant une tente ouverte. Il vous remet une autorisation de traverser les lignes sans détourner les hommes de leur mission.", "Parler au général Desaix"),
("Le jardin irrigué", "Un jardinier ferme successivement les petites vannes. Son récit confirme qu'un canal secondaire peut rejoindre le village recherché.", "Examiner la vanne du jardin"),
("Les marches du débarcadère", "Une volée de marches descend sous les palmiers. Une trace de cire rouge reste collée à la dernière pierre sèche.", "Descendre l'escalier vers la barque"),
("Le bac de la rive orientale", "Youssef attend le retour du bac. De l'autre côté, deux itinéraires rejoignent un caravansérail sans traverser le camp militaire.", "Prendre le bac"),
("Le caravansérail", "Salma demande aux voyageurs s'ils ont vu un étui marqué d'un compas. Un marchand reconnaît l'objet et indique la cour intérieure.", "Parler à Salma dans la cour"),
("La chambre aux tapis", "Une fenêtre donne sur les toits. Sous un tapis roulé, vous trouvez un brouillon qui décrit le débit de plusieurs puits.", "Examiner le brouillon sous le tapis"),
("Les toits de briques", "Un trafiquant surveille un escalier pour empêcher qu'on le suive. Une échelle de maçon permet de contourner son poste.", "Grimper par l'échelle du maçon"),
("Le four du boulanger", "Le boulanger reconnaît le cachet du brouillon. Son voisin grave les sceaux des négociants et travaille encore malgré la chaleur.", "Prendre le sentier vers l'atelier"),
("L'atelier des sceaux", "Farid demande à voir la marque de cire. Il remarque une entaille qui identifie un faux sceau utilisé pour détourner les convois.", "Parler à Farid"),
("La nuit sur la terrasse", "Les étoiles se reflètent dans les bassins du toit. Salma relie les indices : les cartes servent à vendre de faux accès aux réserves d'eau.", "Observer les étoiles avant le départ"),
("La route d'Embabeh", "Les nouvelles de l'armée vous rattrapent sur la route. Vous devez atteindre les intendants avant que le prochain convoi ne suive une fausse carte.", "Suivre le sentier vers Embabeh"),
("Les carrés de toile", "Des officiers disposent des morceaux de toile sur une table pour expliquer leurs mouvements. Un messager vous indique où retrouver Bonaparte après le conseil.", "Examiner la table des officiers"),
("La tente du général", "Napoléon Bonaparte attend un rapport précis. Il exige des preuves du détournement et vous laisse choisir comment protéger le convoi civil.", "Parler à Napoléon Bonaparte"),
("La levée de terre", "Le fracas lointain de la bataille trouble les porteurs. Votre mission reste de guider les civils vers un passage à couvert, loin des affrontements.", "Suivre le passage derrière la levée"),
("Le dépôt disputé", "Un homme armé tente de déplacer les réserves sous couvert du désordre. Salma propose de demander l'aide du magasinier plutôt que de l'affronter.", "Parler au magasinier pour protéger les réserves"),
("Le refuge des familles", "Amina attend près d'un puits dont la corde s'est rompue. Vous pouvez rejoindre les charpentiers pour remettre le passage en service.", "Prendre le chemin des charpentiers"),
("La passerelle démontée", "Les charpentiers assemblent les planches récupérées. Ils ont aperçu un homme portant l'étui des cartes vers le rivage.", "Monter sur la passerelle"),
("Le départ des felouques", "Youssef a trouvé une embarcation légère. Les fugitifs ont pris le bras du fleuve qui longe les ruines d'un ancien quai.", "Monter dans la felouque"),
("Les colonnes du vieux quai", "Des colonnes brisées émergent du sable. Une inscription moderne, griffonnée à la craie, donne rendez-vous près du Caire.", "Examiner la colonne marquée"),
("La porte du Caire", "Salma s'entretient avec un responsable du quartier. Il accepte de vous guider si l'enquête ne devient pas un prétexte pour saisir les réserves des habitants.", "Parler à Salma et au responsable"),
("La cour des fontaines", "L'eau circule entre plusieurs bassins de pierre. Farid identifie sur une jarre le même faux sceau que celui du carnet.", "Examiner la jarre au faux sceau"),
("L'escalier du copiste", "Un copiste conserve les doubles des contrats de transport. Une page a été retirée si récemment que l'encre du feuillet voisin reste humide.", "Monter l'escalier du copiste"),
("Le coffre des contrats", "Un complice revient chercher le dernier contrat. Le copiste vous montre une cache d'où vous pouvez laisser passer l'homme et lire les documents.", "Ouvrir le coffre des contrats"),
("La loggia de Monge", "Gaspard Monge attend devant un relevé incomplet. Il confirme que le carnet mêle des mesures utiles à des indications volontairement fausses.", "Parler à Gaspard Monge"),
("Le jardin des instruments", "Les savants alignent leurs instruments sur une table. Salma propose de comparer les orientations du carnet à celles de la plaine de Gizeh.", "Observer avec la longue-vue des savants"),
("La barque de Gizeh", "Youssef attend sur la rive ouest. Les pyramides se détachent enfin de la poussière, au-delà des cultures et des palmiers.", "Prendre la barque vers Gizeh"),
("Au pied des pyramides", "Salma examine une pierre qui sert de repère aux arpenteurs. Le dessin volé indique une citerne proche des voies anciennes, pas une salle secrète dans la pyramide.", "Examiner la pierre des arpenteurs"),
("Les colonnes du temple", "Le vent siffle entre les colonnes. Un morceau d'étui dépasse du sable près d'une marche où quelqu'un s'est assis récemment.", "Monter l'escalier du temple"),
("Le camp des ouvriers", "Farid attend avec deux ouvriers qui entretiennent les accès à l'eau. Ils ont vu les suspects descendre vers un magasin à l'écart des monuments.", "Parler à Farid et aux ouvriers"),
("La galerie fraîche", "Une galerie de service protège les jarres du soleil. Les traces récentes s'arrêtent devant un battant de bois fermé de l'intérieur.", "Examiner la serrure de la galerie"),
("Le gardien du magasin", "Le chef du trafic garde le dernier carnet. Salma veut négocier sa remise pendant que les ouvriers sécurisent le passage vers le puits.", "Parler au gardien pour récupérer le carnet"),
("La citerne", "Vous retrouvez le plan complet sur une table basse. Les fausses indications peuvent être corrigées, mais il faut encore distinguer les relevés fiables.", "Examiner la carte près de la citerne"),
("Le relevé des ombres", "Salma compare les ombres aux mesures de Monge. La véritable route de l'eau rejoint un village que les convois n'avaient pas prévu de desservir.", "Observer les ombres avec la longue-vue"),
("Le retour au village", "Amina attend sur la place. Les habitants demandent que les cartes corrigées leur soient remises en même temps qu'à l'armée.", "Parler à Amina sur la place"),
("Les copies du plan", "Le copiste étend plusieurs feuilles sur une table. Vous préparez deux versions lisibles du relevé afin qu'aucun groupe ne dépende d'un exemplaire unique.", "Examiner les copies du plan"),
("Le dernier passage du Nil", "Youssef charge les documents dans une caisse étanche. La traversée vous ramène au camp avec les témoignages des villages.", "Monter dans la barque chargée de documents"),
("Le conseil du soir", "Napoléon Bonaparte attend avec les intendants. Votre rapport distingue les faits établis des rumeurs qui ont accompagné l'enquête.", "Parler à Napoléon Bonaparte au conseil"),
("Les engagements écrits", "Salma demande que les accords d'accès à l'eau soient écrits. Un officier accepte de faire porter un double au village avant le départ du convoi.", "Examiner les engagements sur la table"),
("Les derniers complices", "Un complice tente encore de récupérer le faux sceau. Farid propose de le remettre aux responsables du quartier avec les preuves du trafic.", "Parler à Farid pour remettre les preuves"),
("La route des réserves", "Le premier convoi emprunte la route corrigée. Vous accompagnez les porteurs jusqu'à l'embranchement qui dessert le village.", "Suivre le chemin du convoi"),
("La lumière sur Gizeh", "Le soleil descend derrière les palmiers et les pyramides. Salma vous rejoint pour décider à qui confier le dernier carnet de terrain.", "Rejoindre Salma par le sentier"),
("Le choix du cartographe", "Deux travaux vous attendent : accompagner les savants dans leurs relevés ou rester auprès des habitants pour entretenir les accès à l'eau. Bonaparte a reçu les cartes ; votre propre route vous appartient.", "Confier le carnet aux savants"),
]


def goto(text, target):
    return {"text": text, "outcome": {"type": "goto", "next": target}}


def assemble():
    hero = {
        "name": "Camille Laurent", "background": "Interprète et cartographe de l'expédition, vous enquêtez avec Salma pour protéger les routes de l'eau.",
        "st": 11, "dx": 12, "iq": 10, "ht": 12,
        "skills": [{"skill": s, "level": n} for s, n in [
            ("broadsword", 14), ("stealth", 13), ("lockpicking", 12),
            ("diplomacy", 11), ("brawling", 12), ("knife", 12)]],
        "weapon": "broadsword", "armor": "leather",
    }
    foe = {"name": "Complice armé", "st": 14, "dx": 11, "iq": 9, "ht": 11,
           "skills": [{"skill": "knife", "level": 15}], "weapon": "largeKnife",
           "armor": "none", "naturalDR": 0}
    risky = {2, 4, 6, 8, 10, 12, 20, 28, 36, 44, 52, 60}
    scenes = []
    for i, (title, text, action) in enumerate(STAGES):
        chapter = ["I · Les cartes volées", "II · Les chemins du Nil",
                   "III · Les preuves du Caire", "IV · L'eau des pyramides"][i // 16]
        choices = [goto(action, i + 1)]
        if i == 63:
            choices = [goto(action, 64), goto("Rejoindre Amina pour entretenir les accès à l'eau", 65)]
        elif i % 4 == 1:
            side = 100 + i
            choices.append(goto("Examiner les objets et les traces du lieu", side))
            scenes.append({
                "id": side, "title": title + " · Le détour",
                "text": text + " Vous prenez le temps d'écouter un autre témoignage et d'en noter les détails. Les lieux peuvent être réexaminés ; poursuivre l'enquête reste votre décision.",
                "choices": [
                    goto("Suivre le sentier pour poursuivre l'enquête", i + 1),
                    goto("Revenir au lieu principal pour comparer les indices", i),
                ],
            })
        elif i not in risky:
            side = 200 + i
            choices.append({
                "text": "Examiner les traces discrètement (Discrétion)",
                "outcome": {"type": "roll", "against": "stealth", "modifier": 0,
                            "onSuccess": i + 1, "onFailure": side},
            })
            scenes.append({
                "id": side, "title": title + " · Une autre piste",
                "text": "Votre approche a attiré l'attention. Salma intervient et obtient le temps d'expliquer la mission ; cette étape vous permet de comparer les témoignages sans imposer un combat.",
                "choices": [goto("Parler à Salma puis reprendre le chemin", i + 1)],
            })
        if i in risky:
            choices.append({"text": "Défier le complice au sabre", "outcome": {
                "type": "fight", "foes": [foe], "onWin": i + 1}})
        scenes.append({"id": i, "title": title, "text": chapter + ". " + text, "choices": choices})
    scenes += [
        {"id": 64, "title": "Fin · Le carnet des savants",
         "text": "Vous accompagnez Salma et les savants dans de nouveaux relevés. Les copies des cartes restent accessibles aux habitants ; votre carnet distingue désormais ce que vous avez mesuré de ce qu'on vous a raconté.", "choices": []},
        {"id": 65, "title": "Fin · Les gardiens de l'eau",
         "text": "Vous restez avec Amina pour transmettre les relevés et réparer les passages. Bonaparte poursuit sa campagne ; votre aventure se termine par un travail partagé dont les villages peuvent garder la maîtrise.", "choices": []},
    ]
    return {
        "title": "Bonaparte · Les Cartes du Nil", "world": "Égypte, campagne de Bonaparte, 1798",
        "intro": "Égypte, juillet 1798. Vous êtes Camille Laurent, interprète et cartographe de l'expédition. Avec Salma, vous recherchez des plans volés qui menacent l'accès à l'eau. Cette fiction historique vous mène des quais d'Alexandrie au Nil, au Caire et aux pyramides de Gizeh.",
        "fairnessProfile": "exploration-10-v1", "character": hero, "start": 0,
        "themeNames": {"skills": [{"skill": "broadsword", "name": "Escrime au sabre"}, {"skill": "stealth", "name": "Discrétion"},
                                  {"skill": "diplomacy", "name": "Négociation"}, {"skill": "lockpicking", "name": "Serrurerie"}],
                       "weapons": [{"weapon": "broadsword", "name": "Sabre de l'expédition"}],
                       "armor": [{"armor": "leather", "name": "Veste renforcée"}]},
        "palette": ["#d9b878", "#b9894d", "#ead9ab", "#254c62", "#193747", "#6d4d35"],
        "scenes": sorted(scenes, key=lambda s: s["id"]),
        "wish": "Une longue aventure avec Napoléon pendant la campagne d'Égypte, au temps de la bataille des Pyramides.",
        "fairnessSeed": 20261103,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', action='store_true', help='Check and install in the local adventure library')
    args = parser.parse_args()
    started = time.perf_counter()
    adventure = assemble()
    destination = ROOT / "campaigns" / "napoleon.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(adventure, ensure_ascii=False, indent=2) + "\n")
    metrics = {"file": str(destination), "scenes": len(adventure["scenes"]),
                      "shortest_successful_path": len(STAGES),
                      "assembly_ms": (time.perf_counter() - started) * 1000,
                      "source": "locally authored text, no generative API"}
    if args.install:
        result = subprocess.run([str(ROOT / '.lake/build/bin/inspect-adventure'), str(destination),
                                 '--horizon', '14', '--seed', str(adventure['fairnessSeed'])],
                                capture_output=True, text=True, check=True)
        report = json.loads(result.stdout)
        folder = ROOT / 'adventures/2-bonaparte-les-cartes-du-nil'
        folder.mkdir(parents=True, exist_ok=True)
        (folder / 'adventure.json').write_bytes(destination.read_bytes())
        metrics.update(validation=report, installed=str(folder),
                       total_ms=(time.perf_counter() - started) * 1000)
        (folder / 'creation-metrics.json').write_text(json.dumps(metrics, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(metrics, ensure_ascii=False))


if __name__ == "__main__":
    main()
